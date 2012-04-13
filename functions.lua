-- Functions table handling.
require('object')


functions = { }

function functions.new(string, f)
   if not functions[string] then   
      funcions[string] = f
   end
   
end

function get_function(verb, subject, object) --Get sword with the tongs - sword = subject, tongs = object

   local x,y,z

   x = helper(verb)
   y = helper(subject)
   z = helper(object)

   for ix,vx in ipairs(x) do

      for iy,vy in ipairs(y) do
	 for iz,vz in ipairs(z) do
	    output = vx .. vy .. vz
	    local f = functions[output:match(".*%S")]
	    if f then
	       return f
	    end

	 end
      end
   end
   return no_function
end


function helper(atom)
   if not atom then
      x = { 
      return { "" }
   else
      return get_all_parents(atom)
   end
end




