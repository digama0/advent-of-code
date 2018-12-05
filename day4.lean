-- https://adventofcode.com/2018/day/4

import .common data.list.sort
open parser

namespace day4

structure day :=
(year : ℕ)
(month : ℕ)
(day : ℕ)

instance day.has_to_string : has_to_string day :=
⟨λ ⟨y, m, d⟩, to_string y ++ "-" ++ to_string m ++ "-" ++ to_string d⟩

structure date :=
(day : day)
(hour : ℕ)
(min : ℕ)

def to_prod : date → ℕ × ℕ × ℕ × ℕ × ℕ
| ⟨⟨y, m, d⟩, h, mm⟩ := (y, m, d, h, mm)

instance : has_lt date := ⟨λ d₁ d₂, to_prod d₁ < to_prod d₂⟩

instance date_lt.decidable : @decidable_rel date (<) :=
by unfold has_lt.lt; apply_instance

instance date.has_to_string : has_to_string date :=
⟨λ ⟨⟨y, m, d⟩, h, mm⟩, to_string [y, m, d, h, mm]⟩

def date_parser : parser date := date.mk <$>
(day.mk <$>
  (ch '[' *> number) <*>
  (ch '-' *> number) <*>
  (ch '-' *> number)) <*>
(ch ' ' *> number) <*>
(ch ':' *> number) <* ch ']'

inductive entry
| guard : ℕ → entry
| asleep : entry
| awake : entry

instance entry.has_to_string : has_to_string entry :=
⟨λ e, match e with
| entry.guard n := "guard " ++ to_string n
| entry.asleep := "asleep"
| entry.awake := "awake"
end⟩

def entry_parser : parser (date × entry) :=
prod.mk <$> date_parser <*>
((entry.guard <$> (str " Guard #" *> number <* str " begins shift")) <|>
 (entry.asleep <$ str " falls asleep") <|>
 (entry.awake <$ str " wakes up"))

def day4 := go "day4.txt" (many (entry_parser <* ch '\n'))

def box := array 1000 (array 1000 nat)

def sort_entries : list (date × entry) → list (date × entry) :=
list.merge_sort (λ e₁ e₂, e₁.1 < e₂.1)

def fold_events1 {α} (f : α → day → ℕ → ℕ → ℕ → α) :
  α × ℕ × option (day × ℕ) → date × entry → α × ℕ × option (day × ℕ)
| (a, old, o)             (d, entry.guard new) := (a, new, none)
| (a, old, o)             (d, entry.asleep)    := (a, old, some (d.day, d.min))
| (a, old, some (day, m)) (d, entry.awake)     := (f a day old m d.min, old, none)
| (a, old, none)          (d, entry.awake)     := (a, old, none)

def fold_events {α} (f : α → day → ℕ → ℕ → ℕ → α) (a : α) (l : list (date × entry)) : α :=
(l.foldl (fold_events1 f) (a, 0, none)).1

def guard_count (m : rbmap ℕ ℕ) (_ : day) (guard : ℕ) (start : ℕ) (End : ℕ) : rbmap ℕ ℕ :=
let n := End - start in m.modify guard n (+n)

def top {α} : α → ℕ → α × ℕ → α × ℕ
| g' v' (g, v) := if v < v' then (g', v') else (g, v)

def add_minutes (start : ℕ) (End : ℕ) : array 60 ℕ → array 60 ℕ :=
modify_many (+1) start (End - start)

def count_minutes (g : ℕ) (a : array 60 ℕ) (_ : day) (guard : ℕ) (start : ℕ) (End : ℕ) : array 60 ℕ :=
if guard = g then add_minutes start End a else a

#eval day4 $ λ es,
  let es' := sort_entries es,
      m := fold_events guard_count (mk_rbmap _ _) es',
      g := (m.fold top (0, 0)).1,
      c := fold_events (count_minutes g) ⟨λ _, 0⟩ es',
      top := (c.iterate (0, 0) top).1 in
  to_string (g * top) -- 146622

def count_all_minutes (m : rbmap ℕ (array 60 ℕ)) (_ : day) (guard : ℕ) (start : ℕ) (End : ℕ) : rbmap ℕ (array 60 ℕ) :=
m.modify guard ⟨λ i, if start ≤ i ∧ i < End then 1 else 0⟩ (add_minutes start End)

#eval day4 $ λ es,
  let es' := sort_entries es,
      m := fold_events count_all_minutes (mk_rbmap _ _) es',
      (g, top) := (m.fold (λ g c r, array.iterate c r (λ i, top (g, i))) ((0, 0), 0)).1 in
  to_string (g * top) -- 31848

end day4
