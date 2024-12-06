import Lean

-- Dominate Syntax
namespace Dominate
declare_syntax_cat dominate
syntax "[dominate|" dominate "]" : term

-- 1/4
-- Create trivial syntax
syntax "trivial" : dominate

#check_failure [dominate| trivial]

-- Create syntax that takes params


-- Create syntax that can take a param or not

-- Create syntax that can take many params

end Dominate
