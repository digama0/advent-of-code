-- https://adventofcode.com/2018/day/3

import .common
open parser

structure entry :=
(id : ℕ)
(left : ℕ)
(top : ℕ)
(width : ℕ)
(height : ℕ)

instance : has_to_string entry :=
⟨λ ⟨i, l, t, w, h⟩, to_string [i, l, t, w, h]⟩

def day3 := go "day3.txt" (many (entry.mk <$>
  (ch '#' *> number) <*>
  (str " @ " *> number) <*>
  (ch ',' *> number) <*>
  (str ": " *> number) <*>
  (ch 'x' *> number) <* ch '\n'))

namespace day3

def box := array 1000 (array 1000 nat)

def insert1 (b : box) (e : entry) : box :=
modify_many (modify_many nat.succ e.left e.width) e.top e.height b

#eval day3 $ λ es,
  let arr : box := es.foldl insert1 ⟨λ _, ⟨λ _, 0⟩⟩ in
  to_string (arr.foldl 0 $ λ a r,
    a.foldl r (λ b n, if b > 1 then n+1 else n)) -- 107663

def all_range {n α} (f : α → bool) : ℕ → ℕ → array n α → bool
| s 0     a := tt
| s (i+1) a := if h : s < n then
    f (a.read ⟨s, h⟩) && all_range (s+1) i a
  else tt

def check1 (b : box) (e : entry) : option ℕ :=
if all_range (all_range (λ n, n ≤ 1) e.left e.width) e.top e.height b
then some e.id else none

#eval day3 $ λ es,
  let arr : box := es.foldl insert1 ⟨λ _, ⟨λ _, 0⟩⟩ in
  to_string (es.foldl (λ (r:option ℕ) e, r <|> check1 arr e) none) -- 1166

end day3
