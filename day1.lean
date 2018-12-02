import .common data.buffer.parser data.list.basic
open parser sum

def day1 := go "day1.txt" (many (signed_number <* ch '\n'))

#eval day1 $ λ l, to_string l.sum

def seen := rbmap ℤ unit

def iter (inp : list ℤ) : ℕ → list ℤ → seen → ℤ → option string
| 0 _ _ _ := none
| (n+1) [] s z := iter n inp s z
| (n+1) (i::l) s z :=
  let j := i + z in
  if s.contains j then
    some (to_string j)
  else iter (n+1) l (s.insert j ()) j

#eval day1 $ λ l, iter l 1000 [] (mk_rbmap _ _) 0
