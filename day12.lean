-- https://adventofcode.com/2018/day/12

import .common data.bitvec data.array.lemmas
open parser

namespace day12

def token : parser bool := (ch '#' $> tt) <|> (ch '.' $> ff)

def tokens : ∀ n, parser (bitvec n)
| 0 := return vector.nil
| (n+1) := vector.cons <$> token <*> tokens n

def day12 := go "day12.txt" $ prod.mk <$>
  (str "initial state: " *> many token <* str "\n\n") <*>
  many (prod.mk <$> (tokens 5 <* str " => ") <*> token <* ch '\n')

def load_rules1 {α} (a : array 32 α) : bitvec 5 × α → array 32 α
| (v, b) := a.write (fin.of_nat (bitvec.to_nat v)) b

structure state :=
(off : ℤ)
(len : ℕ)
(arr : array len bool)

def state.read : state → ℤ → bool
| ⟨off, _, a⟩ n :=
  match n - off with
  | (i : ℕ) := ∃ h, a.read ⟨i, h⟩
  | _ := ff
  end

def state.next (rules : array 32 bool) (s : state) (i : ℤ) : bool :=
rules.read (fin.of_nat (bitvec.to_nat $
  s.read (i-2) :: s.read (i-1) :: s.read i :: s.read (i+1) :: s.read (i+2) :: vector.nil))

def wrap (f : ℤ → bool) : ℤ → ℕ → state
| off 0 := ⟨off, 0, ⟨λ _, ff⟩⟩
| off (len+1) :=
  if f off then
    if f (len + off) then
      ⟨off, len+1, ⟨λ i, f (i.1 + off)⟩⟩
    else wrap off len
  else wrap (off+1) len

def state.of_list (l : list bool) : state :=
let ⟨n, arr⟩ := l.to_buffer in wrap (state.read ⟨0, n, arr⟩) 0 n

def step (rules : array 32 bool) : state → state
| s@⟨off, len, arr⟩ := wrap (s.next rules) (off-2) (len + 4)

def show_state : ℤ → state → string
| o s := match s.off - o with
  | (i : ℕ) := list.as_string (list.repeat ' ' (i + 1))
  | _ := "<"
  end ++ let diff := int.to_nat (o - s.off) in
    list.as_string ((list.range (s.len - diff)).map
      (λ n, if s.arr.read' (n + diff) then '#' else '.'))

def run (rules : array 32 bool) : ℕ → state → state
| 0 s := trace (show_state (-10) s) s
| (n+1) s := trace (show_state (-10) s) (run n (step rules s))

def state.sum {α} [add_monoid α] (f : ℤ → α) : state → α
| ⟨off, len, arr⟩ :=
  arr.iterate 0 (λ i b a, if b then a + f (i.1 + off) else a)

#eval day12 $ λ ⟨start, rules⟩, do
  let rules := rules.foldl load_rules1 ⟨λ _, ff⟩,
  guard (rules.read 0 = ff),
  let init := state.of_list start,
  let res := run rules 20 init,
  some $ to_string (res.sum id)

-- Note this is not completely general, although it works on my input.
-- Some cellular automata have crazy complicated behavior in the long
-- term, but mine eventually settles down to a bunch of rightward rays like so:
-- ..#.....#..#..#....#
-- ...#.....#..#..#....#
-- ....#.....#..#..#....#
def stabilize (rules : array 32 bool) : ℕ → ℕ → state → option (ℕ × ℤ × state)
| 0 i s := none
| (n+1) i s :=
  let s' := step rules s in
  if (⟨_, s'.arr⟩ : buffer _) = ⟨_, s.arr⟩ then
    some (i+1, s'.off - s.off, s')
  else stabilize n (i+1) (step rules s)

#eval day12 $ λ ⟨start, rules⟩, do
  let rules := rules.foldl load_rules1 ⟨λ _, ff⟩,
  guard (rules.read 0 = ff),
  let init := state.of_list start,
  (n, off1, ⟨off, len, res⟩) ← stabilize rules 500 0 init,
  let final : state := ⟨off + (50000000000 - n) * off1, len, res⟩,
  some $ to_string (n, off1, final.sum id)

end day12
