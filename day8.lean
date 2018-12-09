-- https://adventofcode.com/2018/day/8

import .common data.nat.basic
open parser

namespace day8

def day8 := go "day8.txt" $
 list.cons <$> number <*> many (ch ' ' *> number) <* ch '\n'

def process : list ℕ → list (ℕ × ℕ) → ℕ → ℕ
| (a :: b :: l) ((n+1, i) :: K) sum := process l ((a, b) :: (n, i) :: K) sum
| (a :: l) ((0, i+1) :: K) sum := process l ((0, i) :: K) (sum + a)
| l ((0, 0) :: K) sum := process l K sum
| _ _ sum := sum

#eval day8 $ λ es, some $ to_string $ process es [(1, 0)] 0

def read (n : ℕ) : option (list ℕ) → ℕ
| none := n
| (some ls) := (nat.ppred n >>= ls.nth).iget

meta mutual def get_child, get_children, get_data
with get_child : list ℕ → option (ℕ × list ℕ)
| (a :: b :: l) := do
  (ls, l') ← get_children a l,
  get_data b l' (if ls = [] then none else ls)
| _ := none
with get_children : ℕ → list ℕ → option (list ℕ × list ℕ)
| (n+1) l := do
  (a, l₁) ← get_child l,
  (ls, l₂) ← get_children n l₁,
  return (a :: ls, l₂)
| 0 l := some ([], l)
with get_data : ℕ → list ℕ → option (list ℕ) → option (ℕ × list ℕ)
| (n+1) (a :: l) ls := do
  (b, l') ← get_data n l ls,
  return (read a ls + b, l')
| 0 l ls := some (0, l)
| _ l _ := none

#eval day8 $ λ es, do
  (n, l) ← get_child es,
  some $ to_string n

end day8
