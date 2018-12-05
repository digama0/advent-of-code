-- https://adventofcode.com/2018/day/5

import .common data.list.basic
open parser

namespace day5

structure date :=
(year : ℕ)
(month : ℕ)
(day : ℕ)
(hour : ℕ)
(min : ℕ)

def to_prod : date → ℕ × ℕ × ℕ × ℕ × ℕ
| ⟨y, m, d, h, mm⟩ := (y, m, d, h, mm)

instance : has_lt date := ⟨λ d₁ d₂, to_prod d₁ < to_prod d₂⟩

instance date_lt.decidable : @decidable_rel date (<) :=
by unfold has_lt.lt; apply_instance

def elem := bool × char

def cased_letter : parser elem :=
(prod.mk tt <$> letter) <|>
((λ c:char, (ff, char.of_nat $ c.val + ('a'.val - 'A'.val))) <$> Letter)

def day5 := go "day5.txt" (many cased_letter <* ch '\n')

def cancels (a b : elem) : bool := a.2 = b.2 ∧ a.1 ≠ b.1

def process : list elem → elem → list elem
| [] e := [e]
| (a::l) e := if cancels a e then l else e::a::l

def react_len (l : list elem) : ℕ := (list.foldl process [] l).length

#eval day5 $ λ es, to_string (react_len es)

def letters : list char :=
char.of_nat <$> list.range' 'a'.val ('z'.val - 'a'.val + 1)

#eval day5 $ λ es,
  let lens : list (with_top ℕ) :=
    letters.map (λ c, react_len (es.filter (λ e, e.2 ≠ c))) in
  let min := lens.foldl (⊓) ⊤ in
  to_string <$> min

end day5
