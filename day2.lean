-- https://adventofcode.com/2018/day/2

import .common data.list.basic
open parser

def day2 := go "day2.txt" (many (many letter <* ch '\n'))

namespace day2

def get_counts (l : list char) : bool × bool :=
let m := list.foldl (λ s c, rbmap.modify s c 1 nat.succ) (mk_rbmap char ℕ) l in
m.fold (λ c n ⟨r₁, r₂⟩, ⟨r₁ ∨ n = 2, r₂ ∨ n = 3⟩) (ff, ff)

#eval day2 $ λ ls, do
  let (l₁, l₂) := (ls.map get_counts).unzip,
  return (to_string (l₁.count tt * l₂.count tt))

def diff1 {α} [decidable_eq α] : list α → list α → option (list α)
| (a::l₁) (b::l₂) := if a = b then
    list.cons a <$> diff1 l₁ l₂
  else option.guard (eq l₁) l₂
| _ _ := none

def diffs {α} [decidable_eq α] : list (list α) → list α
| (l :: ls) := match ls.filter_map (diff1 l) with
  | [r] := r
  | _ := diffs ls
  end
| [] := []

#eval day2 $ λ ls, some (list.as_string (diffs ls))

end day2
