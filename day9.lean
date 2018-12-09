-- https://adventofcode.com/2018/day/9

import .common data.nat.basic
open parser

namespace day9

def day9 := go "day9.txt" $
  prod.mk <$> (number <* str " players; last marble is worth ") <*>
  number <* str " points\n"

structure circle (α : Type*) :=
(left : list α) (active : α) (right : list α)

def rotate_right {α} : circle α → circle α
| ⟨l, a, b::r⟩ := ⟨a::l, b, r⟩
| ⟨l, a, []⟩ := match list.reverse l with
  | (b :: r) := ⟨[a], b, r⟩
  | [] := ⟨[], a, []⟩
  end

def split {α} (n : ℕ) : list α → list α × dlist α ⊕ ℕ
| [] := sum.inr n
| (b :: l) :=
  match split l with
  | sum.inr (n+1) := sum.inr n
  | sum.inr 0 := sum.inl ([b], dlist.of_list l)
  | sum.inl (l', r) := sum.inl (b :: l', r)
  end

-- TODO: this doesn't have to be meta but it doesn't terminate on empty
meta def split' {α} (r : list α) : ℕ → list α × dlist α
| n := match split n r with
  | sum.inl res := res
  | sum.inr n' := split' n'
  end

meta def rotate_left {α} : ℕ → circle α → circle α
| 0 c := c
| (n+1) ⟨b::l, a, r⟩ := rotate_left n ⟨l, b, a::r⟩
| (n+1) ⟨[], a, r⟩ :=
  let (r', l) := split' (a::r) (n+1) in
  match l.apply r' with
  | b :: r₂ := ⟨[], b, r₂⟩
  | [] := ⟨[], a, r⟩ -- impossible
  end

meta def pop_right {α} [inhabited α] : circle α → α × circle α
| ⟨l, a, b::r⟩ := (a, ⟨l, b, r⟩)
| ⟨l, a, []⟩ := match list.reverse l with
  | (b :: r) := (a, ⟨[], b, r⟩)
  | [] := (default _, ⟨[], a, []⟩)
  end

def insert_right {α} (n : α) : circle α → circle α
| ⟨l, a, r⟩ := ⟨a :: l, n, r⟩

meta def play1 {p} (n n' : ℕ) : ℕ × circle ℕ × array (p+1) ℕ → ℕ × circle ℕ × array (p+1) ℕ
| (i+1, c, ps) := (i, insert_right n (rotate_right c), ps)
| (0, c, ps) := let (a, c') := pop_right (rotate_left 7 c) in
  (22, c', ps.modify (fin.of_nat n') (+ n + a))

meta def play (p) : ℕ → ℕ × circle ℕ × array (p+1) ℕ
| 0 := (22, ⟨[], 0, []⟩, ⟨λ _, 0⟩)
| n@(n'+1) := play1 n n (play n')

meta def highscore (ps : ℕ) (n : ℕ) : ℕ :=
let (_, _, a) := play (ps-1) n in
array.iterate a 0 (λ _, max)

#eval day9 $ λ ⟨ps, n⟩, some $ to_string (highscore ps n)

-- only runs in console lean, times out in interactive mode
#eval day9 $ λ ⟨ps, n⟩, some $ to_string (highscore ps (100 * n))

end day9
