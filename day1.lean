import .common data.list.basic
open parser sum

def day1 := go "day1.txt" (many (signed_number <* ch '\n'))

namespace day1

#eval day1 $ λ l, to_string l.sum -- 427

/- non meta with a depth limiter -/
def iter (inp : list ℤ) : ℕ → list ℤ → rbmap ℤ unit → ℤ → option string
| 0 _ _ _ := none
| (n+1) [] s z := iter n inp s z
| (n+1) (i::l) s z :=
  let j := i + z in
  if s.contains j then
    some (to_string j)
  else iter (n+1) l (s.insert j ()) j

#eval day1 $ λ l, iter l 1000 [] (mk_rbmap _ _) 0 -- 341

/- no depth limiter -/
meta def iter2 (inp : list ℤ) : list ℤ → rbmap ℤ unit → ℤ → string
| [] s z := iter2 inp s z
| (i::l) s z :=
  let j := i + z in
  if s.contains j then to_string j
  else iter2 l (s.insert j ()) j

#eval day1 $ λ l, iter2 l [] (mk_rbmap _ _) 0 -- 341

end day1
