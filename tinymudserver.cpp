/*

 tinymudserver - an example MUD server

 Author:  Nick Gammon 
          http://www.gammon.com.au/ 

 Date:    22nd July 2004

(C) Copyright Nick Gammon 2004. Permission to copy, use, modify, sell and
distribute this software is granted provided this copyright notice appears
in all copies. This software is provided "as is" without express or implied
warranty, and with no claim as to its suitability for any purpose.
 
*/

#include <fcntl.h>
#include <signal.h>
#include <sys/time.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/errno.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <unistd.h>

// standard library includes ...

#include <string>
#include <list>
#include <map>
#include <set>
#include <vector>
#include <stdexcept>
#include <fstream>
#include <iostream>
#include <sstream>
#include <ios>
#include <iterator>

using namespace std; 

// configuration constants

static const string VERSION = "2.0.0";        // server version
static const int PORT = 4000;                 // incoming connections port
static const string PROMPT = "> ";            // normal player prompt
static const int INITIAL_ROOM = 1000;         // what room they start in
static const int MAX_PASSWORD_ATTEMPTS = 3;   // times they can try a password
static const int MESSAGE_INTERVAL = 60;       // seconds between tick messages
// This is the time the "select" waits before timing out.
static const long COMMS_WAIT_SEC = 0;         // time to wait in seconds
static const long COMMS_WAIT_USEC = 500000;   // time to wait in microseconds
static const int NO_SOCKET = -1;              // indicator for no socket connected
// files
static const string PLAYER_DIR    = "./players/";    // location of player files
static const string PLAYER_EXT    = ".player";       // suffix for player files
static const char * MESSAGES_FILE = "./system/messages.txt";  // messages
static const char * CONTROL_FILE  = "./system/control.txt";   // control file
static const char * ROOMS_FILE    = "./rooms/rooms.txt";      // rooms file
// player names must consist of characters from this list
static const string valid_player_name = 
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_-";
static const string SPACES = " \t\r\n";           // what gets removed when we trim

// make a string on-the-fly
#define MAKE_STRING(msg) \
   (((ostringstream&) (ostringstream() << boolalpha << msg)).str())

// global variables
static bool   bStopNow = false;      // when set, the MUD shuts down
static time_t tLastMessage = 0;      // time we last sent a periodic message 
static int    iControl = NO_SOCKET;  // socket for accepting new connections 
// comms descriptors
static fd_set in_set;  
static fd_set out_set;
static fd_set exc_set;
 
/* connection states - add more to have more complex connection dialogs */
typedef enum
{
  eAwaitingName,        // we want their player name
  eAwaitingPassword,    // we want their old password
  
  eAwaitingNewName,     // they have typed 'new' and are being asked for a new name
  eAwaitingNewPassword, // we want a new password
  eConfirmPassword,     // confirm the new password
  
  ePlaying              // this is the normal 'connected' mode
} tConnectionStates;

// case-independent (ci) string compare
// returns true if strings are EQUAL
struct ciEqualTo : binary_function <string, string, bool>
  {
  struct compare_equal 
    : public binary_function <unsigned char, unsigned char,bool>
    {
    bool operator() (const unsigned char& c1, const unsigned char& c2) const
      { return tolower (c1) == tolower (c2); }
    };  // end of compare_equal

  bool operator() (const string & s1, const string & s2) const
    {
    pair <string::const_iterator, string::const_iterator> result =
      mismatch (s1.begin (), s1.end (), s2.begin (), compare_equal ()); 

    // match if both at end
    return result.first == s1.end () && result.second == s2.end ();
    }
  }; // end of ciEqualTo

// case-independent (ci) string less_than
// returns true if s1 < s2
struct ciLess : binary_function <string, string, bool>
  {
  // case-independent (ci) compare_less binary function
  struct compare_less 
    : public binary_function <unsigned char, unsigned char,bool>
    {
    bool operator() (const unsigned char& c1, const unsigned char& c2) const
      { return tolower (c1) < tolower (c2); }
    }; // end of compare_less

  bool operator() (const string & s1, const string & s2) const
    {
    return lexicographical_compare
          (s1.begin (), s1.end (), s2.begin (), s2.end (), compare_less ()); 
    }
  }; // end of ciLess

// string find-and-replace
string FindAndReplace
  (const string& source, const string target, const string replacement)
  {
  string str = source;
  string::size_type pos = 0,   // where we are now
                    found;     // where the found data is
  if (target.size () > 0)   // searching for nothing will cause a loop
    while ((found = str.find (target, pos)) != string::npos)
      {
      str.replace (found, target.size (), replacement);
      pos = found + replacement.size ();
      }
  return str;
  };   // end of FindAndReplace

/*---------------------------------------------- */
/*  player class - holds details about each connected player */
/*---------------------------------------------- */

class tPlayer
{
private:
  int s;              // socket they connected on
  int port;           // port they connected on
 
  string outbuf;      // pending output
  string inbuf;       // pending input
  string address;     // address player is from

public:
  tConnectionStates connstate;      /* connection state */
  string prompt;      // the current prompt
  string playername;  // player name
  string password;    // their password
  int badPasswordCount;   // password guessing attempts
  int room;         // what room they are in
  bool closing;     // true if they are about to leave us
  set<string, ciLess> flags;  // player flags

  tPlayer (const int sock, const int p, const string a) 
    : s (sock), port (p), address (a), closing (false)  
      { Init (); } // ctor
  
  ~tPlayer () // dtor
    {
    ProcessWrite ();    // send outstanding text
    if (s != NO_SOCKET) /* close connection if active */
      close (s);
    if (connstate == ePlaying)
      Save ();          // auto-save on close
    };
  
  void Init ()
    {
    connstate = eAwaitingName;
    room = INITIAL_ROOM;
    flags.clear ();
    prompt = "Enter your name, or 'new' to create a new character ...  "; 
    }
    
  // what's our socket?
  int GetSocket () const { return s; }
  // true if connected at all
  bool Connected () const { return s != NO_SOCKET; }
  // true if this player actively playing
  bool IsPlaying () const { return Connected () && connstate == ePlaying && !closing; }
  // true if we have something to send them
  bool PendingOutput () const { return !outbuf.empty (); }

  // output to player (any type)
  template<typename T>
  tPlayer & operator<< (const T & i)  
    {     
    outbuf += MAKE_STRING (i); 
    return *this; 
    };  
  
  void ClosePlayer () { closing = true; }    // close this player's connection
  
  void ProcessRead ();    // get player input
  void ProcessWrite ();   // output outstanding text
  void ProcessException (); // exception on socket
  void Load ();           // load player from disk
  void Save ();           // save player to disk

  tPlayer * GetPlayer (istream & sArgs, 
                      const string & noNameMessage = "Do that to who?", 
                      const bool & notme = false);
  
  bool HaveFlag   (const string & name);  // is flag set?
  void NeedFlag   (const string & name);  // flag must be set
  void NeedNoFlag (const string & name);  // flag must not be set
  
  void DoCommand (const string & command);  // simulate player input (eg. look)
  string GetAddress () const { return address; }  // return player IP address
  
};
  
// player list type
typedef list <tPlayer*> tPlayerList;
typedef tPlayerList::iterator tPlayerListIterator;
// an action handler (commands, connection states)
typedef void (*tHandler) (tPlayer * p, istream & args) ;
// map of exits for rooms
typedef map<string, int> tExitMap;

// a room (vnum of room is in the room map)
class tRoom   
  {
  public:
  
  string description;   // what it looks like
  tExitMap exits;       // map of exits

  // ctor
  tRoom (const string & s) : description (s) {}
  };  // end of class tRoom

// we will use a map of rooms
typedef map <int, tRoom*> tRoomMap;
typedef tRoomMap::const_iterator tRoomMapIterator;
  
// see Josuttis p12 and Meyers p38
struct DeleteObject
  {
  template <typename T>
  void operator() (const T* ptr) const { delete ptr; };
  };
// similar concept for maps
struct DeleteMapObject
  {
  template <typename T>
  void operator() (const T item) const { delete item.second; };
  };
  
// get rid of leading and trailing spaces from a string
string Trim (const string & s, const string & t = SPACES)
{
  string d = s; 
  string::size_type i = d.find_last_not_of (t);
  if (i == string::npos)
    return "";
  else
   return d.erase (i + 1).erase (0, s.find_first_not_of (t)) ; 
}

// returns a lower case version of the string 
string tolower (const string & s)
  {
string d = s;
  transform (d.begin (), d.end (), d.begin (), (int(*)(int)) tolower);
  return d;
  }  // end of tolower

// transformation function for tocapitals that has a "state"
// so it can capitalise a sequence
class fCapitals : public unary_function<unsigned char,unsigned char> 
  {
  bool bUpper;

  public:

  // first letter in string will be in capitals
  fCapitals () : bUpper (true) {}; // constructor

  unsigned char operator() (const unsigned char & c)  
    { 
    unsigned char c1;
    // capitalise depending on previous letter
    if (bUpper)
      c1 = toupper (c);
    else
      c1 = tolower (c);

    // work out whether next letter should be capitals
    bUpper = isalnum (c) == 0;
    return c1; 
    }
  };  // end of class fCapitals

// returns a capitalized version of the string 
string tocapitals (const string & s)
  {
string d = s;
  transform (d.begin (), d.end (), d.begin (), fCapitals ());
  return d;
  }  // end of tocapitals
  
// compare strings for equality using the binary function above
// returns true is s1 == s2
bool ciStringEqual (const string & s1, const string & s2)
  {
  return ciEqualTo () (s1, s2);
  }  // end of ciStringEqual
  
// functor to help finding a player by name
struct findPlayerName
{
  const string name;
  // ctor
  findPlayerName (const string & n) : name ( n ) {} 
  // check for player with correct name, and actually playing
  bool operator() (const tPlayer * p) const
    {
    return p->IsPlaying () && ciStringEqual (p->playername, name);
    } // end of operator()  
};  // end of findPlayerName

/* Some globals  */

// list of all connected players
tPlayerList playerlist;   
// map of all rooms
tRoomMap roommap;
// map of known commands (eg. look, quit, north etc.)
map<string, tHandler> commandmap;
// map of things to do for various connection states
map<tConnectionStates, tHandler> statemap;
// messages
map<string, string, ciLess> messagemap;
// directions
set<string, ciLess> directionset;
// bad player names
set<string, ciLess> badnameset;
// blocked IP addresses
set<string> blockedIP;

/* find a player by name */

tPlayer * FindPlayer (const string & name)
{
  tPlayerListIterator i =
    find_if (playerlist.begin (), playerlist.end (), findPlayerName (name));

  if (i == playerlist.end ())
    return NULL;
  else
    return *i;
  
} /* end of FindPlayer */

tRoom * FindRoom (const int & vnum)
{
  tRoomMapIterator roomiter = roommap.find (vnum);
  
  if (roomiter == roommap.end ())
    throw runtime_error (MAKE_STRING ("Room number " << vnum << " does not exist."));

  return roomiter->second;
}

// helper function for say, tell, chat, etc.
string GetMessage (istream & sArgs, const string & noMessageError)
  {
  string message;
  sArgs >> ws;  // skip leading spaces
  getline (sArgs, message); // get rest of line
  if (message.empty ()) // better have something
    throw runtime_error (noMessageError);
  return message;  
  } // end of GetMessage
  
// helper function for get a flag
string GetFlag (istream & sArgs, const string & noFlagError)
  {
  string flag;
  sArgs >> ws >> flag;
  if (flag.empty ())
    throw runtime_error (noFlagError);
  if (flag.find_first_not_of (valid_player_name) != string::npos)
    throw runtime_error ("Flag name not valid.");
  return flag;      
  } // end of GetFlag 
  
// member function to find another playing, including myself
tPlayer * tPlayer::GetPlayer (istream & args, const string & noNameMessage, const bool & notme)
{
  string name;
  args >> name;  
  if (name.empty ())
    throw runtime_error (noNameMessage);
  tPlayer * p = this;
  if (ciStringEqual (name, "me") || ciStringEqual (name, "self"))
    p = this;
  else
    p = FindPlayer (name);
  if (p == NULL)
    throw runtime_error (MAKE_STRING ("Player " << tocapitals (name) << " is not connected."));
  if (notme && p == this)
    throw runtime_error ("You cannot do that to yourself.");
  return p;  
} // end of GetPlayer

/* Here when a signal is raised */

void bailout (int sig)
{
  cout << "**** Terminated by player on signal " << sig << " ****" << endl << endl;
  bStopNow = true;
} /* end of bailout */

/* set up comms - get ready to listen for connection */

int InitComms ()
  {
  struct sockaddr_in sa;
    
  try
    {
  
    // Create the control socket
    if ( (iControl = socket (AF_INET, SOCK_STREAM, 0)) == -1)
      throw runtime_error ("creating control socket");
    
    // make sure socket doesn't block
    if (fcntl( iControl, F_SETFL, FNDELAY ) == -1)
      throw runtime_error ("fcntl on control socket");
  
    struct linger ld = linger ();  // zero it
  
    // Don't allow closed sockets to linger
    if (setsockopt( iControl, SOL_SOCKET, SO_LINGER,
                    (char *) &ld, sizeof ld ) == -1)
      throw runtime_error ("setsockopt (SO_LINGER)");

    int x = 1;

    // Allow address reuse 
    if (setsockopt( iControl, SOL_SOCKET, SO_REUSEADDR,
                   (char *) &x, sizeof x ) == -1)
      throw runtime_error ("setsockopt (SO_REUSEADDR)");
    
    sa.sin_family       = AF_INET;
    sa.sin_port         = htons (PORT);
    sa.sin_addr.s_addr  = INADDR_ANY;   /* change to listen on a specific adapter */
  
    // bind the socket to our connection port
    if ( bind (iControl, (struct sockaddr *) &sa, sizeof sa) == -1)
      throw runtime_error ("bind");
    
    // listen for connections
  
    if (listen (iControl, SOMAXCONN) == -1)   // SOMAXCONN is the backlog count
      throw runtime_error ("listen");
  
    tLastMessage = time (NULL);
    }  // end of try block
    
  // problem?
  catch (runtime_error & e)
    {
    cerr << "Cannot initialise comms ..." << endl;
    perror (e.what ());
    return 1;    
    }

  // standard termination signals
  signal (SIGINT,  bailout);
  signal (SIGTERM, bailout);
  signal (SIGHUP,  bailout);

  return 0;
  }   /* end of InitComms */


/* close listening port */

void CloseComms ()
  {

  cerr << "Closing all comms connections." << endl;

  // close listening socket
  if (iControl != NO_SOCKET)
    close (iControl);

  // delete all players - this will close connections
  for_each (playerlist.begin (), playerlist.end (), DeleteObject ());

  // delete all rooms
  for_each (roommap.begin (), roommap.end (), DeleteMapObject ());
 
  } /* end of CloseComms */

// functor for sending messages to all players
struct sendToPlayer
{
  const string message;
  const tPlayer * except;
  const int room;
  
  // ctor
  sendToPlayer (const string & m, const tPlayer * e = NULL, const int r = 0) 
      : message (m), except (e), room (r) {}
  // send to this player
  void operator() (tPlayer * p) 
    {
    if (p->IsPlaying () && p != except && (room == 0 || p->room == room))
      *p << message;
    } // end of operator()  
};  // end of sendToPlayer

// send message to all connected players
// possibly excepting one (eg. the player who said something)
// possibly only in one room (eg. for saying in a room)
void SendToAll (const string & message, const tPlayer * ExceptThis = NULL, const int InRoom = 0)
{
  for_each (playerlist.begin (), playerlist.end (), 
            sendToPlayer (message, ExceptThis, InRoom)); 
} /* end of SendToAll */

void PlayerToRoom (tPlayer * p,       // which player
                  const int & vnum,   // which room
                  const string & sPlayerMessage,  // what to tell the player
                  const string & sOthersDepartMessage,  // tell people in original room 
                  const string & sOthersArrriveMessage) // tell people in new room
{
  tRoom * r = FindRoom (vnum); // find the destination room (throws exception if not there)
  SendToAll (sOthersDepartMessage, p, p->room);  // tell others where s/he went
  p->room = vnum;  // move to new room
  *p << sPlayerMessage; // tell player
  p->DoCommand ("look");   // look around new room  
  SendToAll (sOthersArrriveMessage, p, p->room);  // tell others ws/he has arrived  
} // end of PlayerToRoom

void DoDirection (tPlayer * p, const string & sArgs)
  {
  // get current room (throws exception if not there)
  tRoom * r = FindRoom (p->room);

  // find the exit
 tExitMap::const_iterator exititer = r->exits.find (sArgs);    

  if (exititer == r->exits.end ())
    throw runtime_error ("You cannot go that way.");

  // move player
  PlayerToRoom (p, exititer->second,
                "You go " + sArgs + "\n",
                p->playername + " goes " + sArgs + "\n",
                p->playername + " enters.\n");
  
  } // end of DoDirection
  
/* process commands when player is connected */

void ProcessCommand (tPlayer * p, istream & sArgs)
{

  string command;
  sArgs >> command >> ws;   // get command, eat whitespace after it
  
  // first see if they have entered a movement command (eg. n, s, e, w)
  set<string>::const_iterator direction_iter = directionset.find (command);
  if (direction_iter != directionset.end ())
    DoDirection (p, command);
  else
    {
    // otherwise, look up command in commands map  
    map<string, tHandler>::const_iterator command_iter = commandmap.find (command);
    if (command_iter == commandmap.end ())
       throw runtime_error ("Huh?");      // don't get it
 
    command_iter->second (p, sArgs);  // execute command (eg. DoLook)
    }
} /* end of ProcessCommand */

void PlayerEnteredGame (tPlayer * p, const string & message)
{
  p->connstate = ePlaying;    // now normal player
  p->prompt = PROMPT;         // default prompt
  *p << "Welcome, " << p->playername << "\n\n"; // greet them
  *p << message;
  *p << messagemap ["motd"];  // message of the day
  p->DoCommand ("look");     // new player looks around

  // tell other players
  SendToAll (
    "Player " + p->playername + " has joined the game from " + p->GetAddress () + ".\n", 
    p);
  
  // log it
  cout << "Player " << p->playername << " has joined the game." << endl;
} // end of PlayerEnteredGame

void ProcessPlayerName (tPlayer * p, istream & sArgs)
{
  string playername;
  sArgs >> playername;

  /* name can't be blank */
  if (playername.empty ())
    throw runtime_error ("Name cannot be blank.");
  
  /* don't allow two of the same name */
  if (FindPlayer (playername))
    throw runtime_error (playername + " is already connected.");

  if (playername.find_first_not_of (valid_player_name) != string::npos)
    throw runtime_error ("That player name contains disallowed characters.");
        
  if (tolower (playername) == "new")
    {
    p->connstate = eAwaitingNewName;
    p->prompt = "Please choose a name for your new character ... ";
    }   // end of new player
  else
    {   // old player
  
    p->playername = tocapitals (playername);
    p->Load ();   // load player so we know the password etc.
    
    p->connstate = eAwaitingPassword;
    p->prompt = "Enter your password ... ";
    p->badPasswordCount = 0;
    } // end of old player
        
} /* end of ProcessPlayerName */

void ProcessNewPlayerName (tPlayer * p, istream & sArgs)
{
  string playername;
  sArgs >> playername;
  
  /* name can't be blank */
  if (playername.empty ())
    throw runtime_error ("Name cannot be blank.");

  if (playername.find_first_not_of (valid_player_name) != string::npos)
    throw runtime_error ("That player name contains disallowed characters.");
        
  // check for bad names here (from list in control file)
  if (badnameset.find (playername) != badnameset.end ())
    throw runtime_error ("That name is not permitted.");
    
  ifstream f ((PLAYER_DIR + tocapitals (playername) + PLAYER_EXT).c_str (), ios::in);
  if (f || FindPlayer (playername))  // player file on disk, or playing without saving yet
    throw runtime_error ("That player already exists, please choose another name.");
  
  p->playername = tocapitals (playername);
  
  p->connstate = eAwaitingNewPassword;
  p->prompt = "Choose a password for " + p->playername + " ... ";  
  p->badPasswordCount = 0;
    
} /* end of ProcessNewPlayerName */

void ProcessNewPassword (tPlayer * p, istream & sArgs)
{
   string password;
   sArgs >> password;
  
  /* password can't be blank */
  if (password.empty ())
    throw runtime_error ("Password cannot be blank.");
  
  p->password = password;
  p->connstate = eConfirmPassword;
  p->prompt = "Re-enter password to confirm it ... ";
    
} /* end of ProcessNewPassword */

void ProcessConfirmPassword (tPlayer * p, istream & sArgs)
{
   string password;
   sArgs >> password;
  
  // password must agree
  if (password != p->password)
    {
    p->connstate = eAwaitingNewPassword;
    p->prompt = "Choose a password for " + p->playername + " ... ";
    throw runtime_error ("Password and confirmation do not agree.");
    }
  
  // that player might have been created while we were choosing a password, so check again
  ifstream f ((PLAYER_DIR + tocapitals (password) + PLAYER_EXT).c_str (), ios::in);
  if (f || FindPlayer (password))  // player file on disk, or playing without saving yet
    {
    p->connstate = eAwaitingNewName;
    p->prompt = "Please choose a name for your new character ... ";  // re-prompt for name
    throw runtime_error ("That player already exists, please choose another name.");
    }
  
  // New player now in the game
  PlayerEnteredGame (p, messagemap ["new_player"]);
         
} /* end of ProcessNewPassword */

void ProcessPlayerPassword (tPlayer * p, istream & sArgs)
{
  try
    {
    string password;
    sArgs >> password;

    /* password can't be blank */
    if (password.empty ())
      throw runtime_error ("Password cannot be blank.");
        
    if (password != p->password)
      throw runtime_error ("That password is incorrect.");

    // check for "blocked" flag on this player
    if (p->HaveFlag ("blocked"))
      {
      p->ClosePlayer ();
      p->prompt = "Goodbye.\n";
      throw runtime_error ("You are not permitted to connect.");
      }
      
    // OK, they're in!
    PlayerEnteredGame (p, messagemap ["existing_player"]);
 
    } // end of try block
    
  // detect too many password attempts
  catch (runtime_error & e)
    {
    if (++p->badPasswordCount >= MAX_PASSWORD_ATTEMPTS)
      {
      *p << "Too many attempts to guess the password!\n";
      p->Init ();
      }
      throw;
    }
    
} /* end of ProcessPlayerPassword */

void NoMore (tPlayer * p, istream & sArgs)
  {
  string sLine;
  getline (sArgs, sLine);
  if (!sLine.empty ())
    throw runtime_error ("Unexpected input: " + sLine);
  } // end of NoMore
  
/* quit */

void DoQuit (tPlayer * p, istream & sArgs)
  {
  NoMore (p, sArgs);  // check no more input
    
  /* if s/he finished connecting, tell others s/he has left */
  
  if (p->connstate == ePlaying)
    {
    *p << "See you next time!\n";
    cout << "Player " << p->playername << " has left the game.\n";
    SendToAll ("Player " + p->playername + " has left the game.\n", p);   
    } /* end of properly connected */

  p->ClosePlayer ();
  } // end of DoQuit

/* look */

void DoLook (tPlayer * p, istream & sArgs)
{
 
  // TODO: add: look (thing)
  NoMore (p, sArgs);  // check no more input
  
  // find our current room, throws exception if not there
  tRoom * r = FindRoom (p->room);
  
  // show room description
  *p << r->description;
  
  // show available exits
  if (!r->exits.empty ())
    {
    *p << "Exits: ";
    for (tExitMap::const_iterator exititer = r->exits.begin ();
         exititer != r->exits.end (); ++exititer)
      *p << exititer->first << " ";
    *p << "\n";        
    }
  
  /* list other players in the same room */
  
  int iOthers = 0;
  for (tPlayerListIterator listiter = playerlist.begin (); 
      listiter != playerlist.end (); 
      listiter++)
    {
    tPlayer *otherp = *listiter;
    if (otherp != p && /* we don't see ourselves */
        otherp->IsPlaying () &&
        otherp->room == p->room)  // need to be in same room
      {
      if (iOthers++ == 0)
        *p << "You also see ";
      else
        *p << ", ";
      *p << otherp->playername;
      }
    }   /* end of looping through all players */

  /* If we listed anyone, finish up the line with a period, newline */
  if (iOthers)
    *p << ".\n";

  
} // end of DoLook

/* say <something> */

void DoSay (tPlayer * p, istream & sArgs)
{
  p->NeedNoFlag ("gagged"); // can't if gagged
  string what = GetMessage (sArgs, "Say what?");  // what
  *p << "You say, \"" << what << "\"\n";  // confirm
  SendToAll (p->playername + " says, \"" + what + "\"\n", 
            p, p->room);  // say it
} // end of DoSay 

/* tell <someone> <something> */

void DoTell (tPlayer * p, istream & sArgs)
{
  p->NeedNoFlag ("gagged"); // can't if gagged
  tPlayer * ptarget = p->GetPlayer (sArgs, "Tell whom?", true);  // who
  string what = GetMessage (sArgs, "Tell " + p->playername + " what?");  // what  
  *p << "You tell " << p->playername << ", \"" << what << "\"\n";     // confirm
  *ptarget << p->playername << " tells you, \"" << what << "\"\n";    // tell them
} // end of DoTell

void DoSetFlag (tPlayer * p, istream & sArgs)
{
  p->NeedFlag ("can_setflag");  // permissions
  tPlayer * ptarget = p->GetPlayer (sArgs, "Usage: setflag <who> <flag>");  // who
  string flag = GetFlag (sArgs, "Set which flag?"); // what
  NoMore (p, sArgs);  // check no more input
  if (ptarget->flags.find (flag) != ptarget->flags.end ())    // check not set
    throw runtime_error ("Flag already set.");
  
  ptarget->flags.insert (flag);   // set it
  *p << "You set the flag '" << flag << "' for " << ptarget->playername << "\n";  // confirm
      
} // end of DoSetFlag

void DoClearFlag (tPlayer * p, istream & sArgs)
{
  p->NeedFlag ("can_setflag");  // permissions
  tPlayer * ptarget = p->GetPlayer (sArgs, "Usage: clearflag <who> <flag>");  // who
  string flag = GetFlag (sArgs, "Clear which flag?"); // what
  NoMore (p, sArgs);  // check no more input
  if (ptarget->flags.find (flag) == ptarget->flags.end ())    // check set
    throw runtime_error ("Flag not set.");

  ptarget->flags.erase (flag);    // clear it
  *p << "You clear the flag '" << flag << "' for " << ptarget->playername << "\n";  // confirm
      
} // end of DoClearFlag

void DoShutdown (tPlayer * p, istream & sArgs)
{
  NoMore (p, sArgs);  // check no more input
  p->NeedFlag ("can_shutdown");
  SendToAll (p->playername + " shuts down the game\n");
  bStopNow = true;
} // end of DoShutdown

void DoHelp (tPlayer * p, istream & sArgs)
{
  NoMore (p, sArgs);  // check no more input
  *p << messagemap ["help"];
} // end of DoHelp

void DoGoTo (tPlayer * p, istream & sArgs)
  {
  p->NeedFlag ("can_goto");

  int room;
  sArgs >> room;
  
  // check room number supplied OK
  if (sArgs.fail ())
    throw runtime_error ("Go to which room?");

  NoMore (p, sArgs);  // check no more input

  // move player
  PlayerToRoom (p, room,
                MAKE_STRING ("You go to room " << room << "\n"),
                p->playername + " disappears in a puff of smoke!\n",
                p->playername + " appears in a puff of smoke!\n");
  
  } // end of DoGoTo
  
void DoTransfer (tPlayer * p, istream & sArgs)
{
  p->NeedFlag ("can_transfer");  // permissions
  tPlayer * ptarget = p->GetPlayer (sArgs, 
    "Usage: transfer <who> [ where ] (default is here)", true);  // who
  int room;
  sArgs >> room;
  
  if (sArgs.fail ())
    room = p->room;   // if no room number, transfer to our room
  
  NoMore (p, sArgs);  // check no more input  

  *p << "You transfer " <<  ptarget->playername << " to room " << room << "\n";
  
   // move player
  PlayerToRoom (ptarget, room,
                p->playername + " transfers you to another room!\n",
                ptarget->playername + " is yanked away by unseen forces!\n",
                ptarget->playername + " appears breathlessly!\n");
     
} // end of DoTransfer
  
/* process player input - check connection state, and act accordingly */

void ProcessPlayerInput (tPlayer * p, const string & s)
{
   try
    {
    istringstream is (s);
              
    // look up what to do in state map  
    map<tConnectionStates, tHandler>::iterator si = statemap.find (p->connstate);
  
    if (si != statemap.end ())
      si->second (p, is);  // execute command (eg. ProcessCommand) 
    } // end of try block

  // all errors during input processing will be caught here
  catch (runtime_error & e)
    {
    *p << e.what () << "\n";    
    }
  
  *p << p->prompt;   // re-prompt them

} /* end of ProcessPlayerInput */

/* new player has connected */

void ProcessNewConnection ()
  {
  static struct sockaddr_in sa;
  socklen_t sa_len = sizeof sa;   

  int s;    /* incoming socket */

  /* loop until all outstanding connections are accepted */
  while (true)
    {
    s = accept ( iControl, (struct sockaddr *) &sa, &sa_len);

    /* a bad socket probably means no more connections are outstanding */
    if (s == NO_SOCKET)
      {

      /* blocking is OK - we have accepted all outstanding connections */
      if ( errno == EWOULDBLOCK )
        return;

      perror ("accept");
      return;
      }
        
    /* here on successful accept - make sure socket doesn't block */
    
    if (fcntl (s, F_SETFL, FNDELAY) == -1)
      {
      perror ("fcntl on player socket");
      return;
      }

    string address = inet_ntoa ( sa.sin_addr);
    int port = ntohs (sa.sin_port);
            
    // immediately close connections from blocked IP addresses
    if (blockedIP.find (address) != blockedIP.end ())
      {
      cerr << "Rejected connection from " << address << endl;
      close (s);
      continue;      
      }
      
    tPlayer * p = new tPlayer (s, port, address);
    playerlist.push_back (p);
    
    cout << "New player accepted on socket " << s << 
            ", from address " << address << 
            ", port " << port << endl;
      
    *p << "\nWelcome to the Tiny MUD Server version " << VERSION << "\n"; 
    *p << messagemap ["welcome"];   // message from message file
    *p << p->prompt;    // initial prompt (Enter your name ...)
    
    } /* end of processing *all* new connections */

  } /* end of ProcessNewConnection */

// load a set of flags from a single line in the input stream "f"
template <class T>
void LoadSet (ifstream & f, T & s)
{
  s.clear ();
  string sLine;
  getline (f, sLine);   // get one line
  istringstream is (sLine); // convert back to stream
  string flag;    // each flag name
  while (!is.eof ())    // read that stream
    {
    is >> flag;   // read flag
    s.insert (flag);  // and insert it
    } // end of getting each item  
} // end of LoadSet
  
void tPlayer::ProcessException ()
{
  /* signals can cause exceptions, don't get too excited. :) */
  cerr << "Exception on socket " << s << endl;
} /* end of tPlayer::ProcessException */

void tPlayer::Load ()
{
  ifstream f ((PLAYER_DIR + playername + PLAYER_EXT).c_str (), ios::in);
  if (!f)
    throw runtime_error ("That player does not exist, type 'new' to create a new one.");
  
  // read player details
  f >> password;
  f >> room;
  f.ignore (numeric_limits<int>::max(), '\n'); // skip rest of this line  
  LoadSet (f, flags);   // player flags (eg. can_shutdown) 
  
} /* end of tPlayer::Load */

void tPlayer::Save ()
{
  ofstream f ((PLAYER_DIR + playername + PLAYER_EXT).c_str (), ios::out);
  if (!f)
  {
  cerr << "Could not write to file for player " << playername << endl;
  return;
  }
  
  // write player details
  f << password << endl;
  f << room << endl;
  copy (flags.begin (), flags.end (), ostream_iterator<string> (f, " "));
  f << endl;
  
} /* end of tPlayer::Save */

void tPlayer::DoCommand (const string & command)
{
  istringstream is (command);
  ProcessCommand (this, is);
} /* end of tPlayer::Load */

// is flag set?
bool tPlayer::HaveFlag (const string & name)
{
  return flags.find (name) != flags.end ();
} // end of NeedFlag

// flag must be set
void tPlayer::NeedFlag (const string & name)
{
  if (!HaveFlag (name))
    throw runtime_error ("You are not permitted to do that.");
} // end of NeedFlag

// flag must not be set
void tPlayer::NeedNoFlag (const string & name)
{
  if (HaveFlag (name))
    throw runtime_error ("You are not permitted to do that.");
} // end of NeedNoFlag


/* Here when there is outstanding data to be read for this player */

void tPlayer::ProcessRead ()
{
  
  if (closing)
    return;   // once closed, don't handle any pending input
  
  // I make it static to save allocating a buffer each time.
  // Hopefully this function won't be called recursively.
  static vector<char> buf (1000);  // reserve 1000 bytes for reading into
  
  int nRead = read (s, &buf [0], buf.size ());
  
  if (nRead == -1)
    {
    if (errno != EWOULDBLOCK)
      perror ("read from player");
    return;
    }

  if (nRead <= 0)
    {
    close (s);
    cerr << "Connection " << s << " closed" << endl;
    s = NO_SOCKET;
    ProcessPlayerInput (this, "quit");  // tell others the s/he has left
    return;
    }

  inbuf += string (&buf [0], nRead);    /* add to input buffer */

  /* try to extract lines from the input buffer */
  for ( ; ; )
    {
    string::size_type i = inbuf.find ('\n');
    if (i == string::npos)
      break;  /* no more at present */

    string sLine = inbuf.substr (0, i);  /* extract first line */
    inbuf = inbuf.substr (i + 1, string::npos); /* get rest of string */

    ProcessPlayerInput (this, Trim (sLine));  /* now, do something with it */        
    }
    
} /* end of tPlayer::ProcessRead */

/* Here when we can send stuff to the player. We are allowing for large
 volumes of output that might not be sent all at once, so whatever cannot
 go this time gets put into the list of outstanding strings for this player. */

void tPlayer::ProcessWrite ()
{
  /* we will loop attempting to write all in buffer, until write blocks */
  while (s != NO_SOCKET && !outbuf.empty ())
    {

    // send a maximum of 512 at a time
    int iLength = min<int> (outbuf.size (), 512);

    // send to player
    int nWrite = write (s, outbuf.c_str (), iLength );

    // check for bad write
    if (nWrite < 0)
      {
      if (errno != EWOULDBLOCK )
        perror ("send to player");  /* some other error? */
      return;
      }

    // remove what we successfully sent from the buffer
    outbuf.erase (0, nWrite);
      
    // if partial write, exit
    if (nWrite < iLength)
       break;

    } /* end of having write loop */

}   /* end of tPlayer::ProcessWrite  */

// prepare for comms
struct setUpDescriptors
{
  int iMaxdesc;
  
  setUpDescriptors (const int i) : iMaxdesc (i) {}
    
  // check this player
  void operator() (const tPlayer * p) 
    {
     /* don't bother if connection is closed */
      if (p->Connected ())
        {
        iMaxdesc = max (iMaxdesc, p->GetSocket ());
        // don't take input if they are closing down
        if (!p->closing)
          {
          FD_SET( p->GetSocket (), &in_set  );
          FD_SET( p->GetSocket (), &exc_set );
          }

        /* we are only interested in writing to sockets we have something for */
        if (p->PendingOutput ())
          FD_SET( p->GetSocket (), &out_set );
        } /* end of active player */
    } // end of operator()  
    
  int GetMax () const { return iMaxdesc; }
  
};  // end of setUpDescriptors

// handle comms
struct processDescriptors
{
  
  // handle this player
  void operator() (tPlayer * p) 
    {
      /* handle exceptions */
      if (p->Connected () && FD_ISSET (p->GetSocket (), &exc_set))
        p->ProcessException ();

      /* look for ones we can read from, provided they aren't closed */
      if (p->Connected () && FD_ISSET (p->GetSocket (), &in_set))
        p->ProcessRead ();

      /* look for ones we can write to, provided they aren't closed */
      if (p->Connected () && FD_ISSET (p->GetSocket (), &out_set))
        p->ProcessWrite ();
     } // end of operator()  
      
};  // end of processDescriptors

void RemoveInactivePlayers ()
{
  for (tPlayerListIterator i = playerlist.begin (); i != playerlist.end (); )
    {
    if (!(*i)->Connected () ||        // no longer connected
         (*i)->closing)               // or about to leave us
      {
      delete *i;
      playerlist.erase (i++);
      }
    else
      ++i;
    } /* end of looping through players */
} // end of RemoveInactivePlayers

// called approximately every 0.5 seconds - handle things like fights here
void PeriodicUpdates ()
  {
    //      The example below just sends a message every MESSAGE_INTERVAL seconds.
    // send new command if it is time
  if (time (NULL) > (tLastMessage + MESSAGE_INTERVAL))
    {
    SendToAll ("You hear creepy noises ...\n");
    tLastMessage = time (NULL);
    }
    
  } // end of PeriodicUpdates
  
// main processing loop
void MainLoop ()
{
  // loop processing input, output, events
  do
    {

    // We will go through this loop roughly every COMMS_WAIT_SEC/COMMS_WAIT_USEC
    // seconds (at present 0.5 seconds).
    PeriodicUpdates ();   // do things that don't rely on player input
      
    // delete players who have closed their comms - have to do it outside other loops to avoid 
    // access violations (iterating loops that have had items removed)
    RemoveInactivePlayers ();
      
    // get ready for "select" function ... 
    FD_ZERO (&in_set);
    FD_ZERO (&out_set);
    FD_ZERO (&exc_set);

    // add our control socket (for new connections)
    FD_SET (iControl, &in_set);

    // set bits in in_set, out_set etc. for each connected player
    int iMaxdesc = for_each (playerlist.begin (), playerlist.end (), 
                             setUpDescriptors (iControl)).GetMax ();
    
    // set up timeout interval
    struct timeval timeout;
    timeout.tv_sec = COMMS_WAIT_SEC;    // seconds
    timeout.tv_usec = COMMS_WAIT_USEC;  // + 1000th. of second

    // check for activity, timeout after 'timeout' seconds
    if (select (iMaxdesc + 1, &in_set, &out_set, &exc_set, &timeout) > 0)
      {
      // New connection on control port?
      if (FD_ISSET (iControl, &in_set))
        ProcessNewConnection ();
      
      // handle all player input/output
      for_each (playerlist.begin (), playerlist.end (), 
                processDescriptors ());      
      } // end of something happened
  
    }  while (!bStopNow);   // end of looping processing input

}   // end of MainLoop

// load things from the control file (directions, prohibited names, blocked addresses)
void LoadControlFile ()
{
  // load control file
  ifstream fControl (CONTROL_FILE, ios::in);
  if (!fControl)
    {
    cerr << "Could not open control file: " << CONTROL_FILE << endl;
    return;
    }

  LoadSet (fControl, directionset); // possible directions, eg. n, s, e, w
  LoadSet (fControl, badnameset);   // bad names for new players, eg. new, quit, look, admin
  LoadSet (fControl, blockedIP);    // blocked IP addresses
} // end of LoadControlFile

// load messages stored on messages file
void LoadMessages ()
{
  // format is: <code> <message>
  //  eg. motd Hi there!
  // Imbedded %r sequences will becomes new lines.
  ifstream fMessages (MESSAGES_FILE, ios::in);
  if (!fMessages)
    {
    cerr << "Could not open messages file: " << MESSAGES_FILE << endl;
    return;
    }

  while (!(fMessages.eof ()))
    {
    string sMessageCode, sMessageText;
    fMessages >> sMessageCode >> ws;
    getline (fMessages, sMessageText);
    if (!(sMessageCode.empty ()))
      messagemap [tolower (sMessageCode)] = 
            FindAndReplace (sMessageText, "%r", "\n");
    } // end of read loop
  
} // end of LoadMessages

// load rooms and exits
void LoadRooms ()
{
  // load rooms file
  ifstream fRooms (ROOMS_FILE, ios::in);
  if (!fRooms)
    {
    cerr << "Could not open rooms file: " << ROOMS_FILE << endl;
    return;
    }
  
  while (!(fRooms.eof ()))
    {
    int vnum;
    fRooms >> vnum;
    fRooms.ignore (numeric_limits<int>::max(), '\n'); // skip rest of this line
    string description;
    getline (fRooms, description);
    
    // give up if no vnum or description
    if (vnum == 0 || description.empty ())
      break;

    // get exits
    string sLine;
    getline (fRooms, sLine); 

    // don't have duplicate rooms
    if (roommap [vnum] != 0)
      {
      cerr << "Room " << vnum << " appears more than once in room file" << endl;
      continue;
      }

    tRoom * room = new tRoom (FindAndReplace (description, "%r", "\n") + "\n");
    roommap [vnum] = room;

    // read exits from line (format is: <dir> <vnum> ...  eg. n 1234 s 5678)
    istringstream is (sLine);
    while (is.good ())
      {
      string dir;
      int dir_vnum;
        
      is >> dir;  // direction, eg. n
      is >> dir_vnum >> ws; // vnum, eg. 1234
      
      if (is.fail ())
        {
        cerr << "Bad vnum for exit " << dir << " for room " << vnum << endl;
        continue;
        }
      
      // direction must be valid (eg. n, s, e, w) or it won't be recognised
      set<string>::const_iterator direction_iter = directionset.find (dir);
      if (direction_iter == directionset.end ())
        {
        cerr << "Direction " << dir << " for room " << vnum 
             << " not in list of directions in control file" << endl;
        continue;
        }
          
      // stop if nonsense
      if (dir.empty () || dir_vnum == 0)
        break;
      
      room->exits [dir] = dir_vnum;   // add exit
     
      } // end of getting each direction      
    } // end of read loop
  
} // end of LoadRooms

// build up our commands map and connection states
void LoadThings ()
{
  // commands
  commandmap ["look"]     = DoLook;     // look around
  commandmap ["l"]        = DoLook;     // synonymm for look
  commandmap ["quit"]     = DoQuit;     // bye bye
  commandmap ["say"]      = DoSay;      // say something
  commandmap ["\""]       = DoSay;      // synonym for say
  commandmap ["tell"]     = DoTell;     // tell someone
  commandmap ["shutdown"] = DoShutdown; // shut MUD down
  commandmap ["help"]     = DoHelp;     // show help message
  commandmap ["goto"]     = DoGoTo;     // go to room
  commandmap ["transfer"] = DoTransfer; // transfer someone else
  commandmap ["setflag"]  = DoSetFlag;  // set a player's flag
  commandmap ["clearflag"]= DoClearFlag;  // clear a player's flag
    
  // connection states
  statemap [eAwaitingName]        = ProcessPlayerName;    // existing player
  statemap [eAwaitingPassword]    = ProcessPlayerPassword;

  statemap [eAwaitingNewName]     = ProcessNewPlayerName; // new player
  statemap [eAwaitingNewPassword] = ProcessNewPassword;
  statemap [eConfirmPassword]     = ProcessConfirmPassword;

  statemap [ePlaying]             = ProcessCommand;   // playing
  
  // load files
  LoadControlFile ();
  LoadMessages ();
  LoadRooms ();
 
} // end of LoadThings

// main program
int main ()
{
  cout << "Tiny MUD server version " << VERSION << endl;

  LoadThings ();    // load stuff
  
  if (InitComms ()) // listen for new connections
    return 1;

  cout << "Accepting connections from port " <<  PORT << endl;
  
  MainLoop ();    // handle player input/output

  // game over - tell them all
  SendToAll ("\n\n** Game shut down. **\n\n");
  
  CloseComms ();  // stop listening

  cout << "Game shut down." << endl;  
  return 0;
}   // end of main
