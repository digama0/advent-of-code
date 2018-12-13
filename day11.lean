-- https://adventofcode.com/2018/day/11

import .common data.list.basic algebra.pi_instances
open parser

@[inline] meta def array.readm {n α} (a : array α n) (i : ℕ) := a.read ⟨i, undefined⟩

namespace day11

def day11 := go "day11.txt" (number <* ch '\n')

def power_level (sn : ℕ) (x y : ℕ) : ℤ :=
let id := x+1 + 10 in (((id * (y+1) + sn) * id / 100) % 10 : ℕ) - 5

instance {α} [has_add α] {n} : has_add (array n α) :=
⟨λ a b, ⟨λ i, a.read i + b.read i⟩⟩

def sum3 {α} [has_add α] {n} (a : array (n + 2) α) : array n α :=
⟨λ i, a.read i + a.read (i+1) + a.read (i+2)⟩

def find_max1 (s x y : ℕ) (n : ℤ) : option (ℤ × ℕ × ℕ × ℕ) → option (ℤ × ℕ × ℕ × ℕ)
| none := some (n, x, y, s)
| (some (n', x', y', s')) := if n' < n then some (n, x, y, s) else some (n', x', y', s')

def find_max (s : ℕ) {m n} (sums : array m (array n ℤ)) (o : option (ℤ × ℕ × ℕ × ℕ)) : option (ℤ × ℕ × ℕ × ℕ) :=
sums.iterate o $ λ y a o, a.iterate o $ λ x n, find_max1 s (x+1) (y+1) n

#eval day11 $ λ sn, do
  let arr : array 300 (array 300 ℤ) := ⟨λ y, ⟨λ x, power_level sn x y⟩⟩,
  let sums := sum3 ⟨λ i, sum3 (arr.read i)⟩,
  (_,x,y,s) ← find_max 3 sums none,
  some (to_string x ++ "," ++ to_string y)

def arr_to_string {m n α} [has_repr α] (arr : array m (array n α)) :=
(arr.foldl "" (λ a r, r ++ repr a.to_list ++ "\n"))

meta def contract {α} [has_add α] [has_repr α]
  {m n} (a : array m (array m α)) :
  array (n + 1) (array (n + 1) α) × array (n + 1) (array (n + 1) α) × array (n + 1) (array (n + 1) α) →
  array n (array n α) × array n (array n α) × array n (array n α)
| (b1, b2, b3) :=
  let c1 : array n (array n α) :=
    ⟨λ y, ⟨λ x, (a.readm y).readm x + (b1.read y).read (x+1)⟩⟩ in
  let c2 : array n (array n α) :=
    ⟨λ y, ⟨λ x, (a.readm y).readm x + (b2.read (y+1)).read x⟩⟩ in
  let c3 : array n (array n α) :=
    ⟨λ y, ⟨λ x, (c2.read y).read x + (b1.read y).read (x+1) + (b3.read (y+1)).read (x+1)⟩⟩ in
  (c1, c2, c3)

meta def check_all {m} (a : array m (array m ℤ)) :
  ∀ {n}, array n (array n ℤ) × array n (array n ℤ) × array n (array n ℤ) →
    ℕ → option (ℤ × ℕ × ℕ × ℕ) → option (ℤ × ℕ × ℕ × ℕ)
| 0 a s o := o
| (n+1) b s o :=
  let o' := find_max s b.2.2 o in
  trace (repr (s, o')) $
  check_all (contract a b) (s+1) o'

-- Lean is clearly not ready for computations of this size.
-- You have to run this one in the console, and I've left in some
-- trace messages with the best found so far.
#eval day11 $ λ sn, do
  let arr : array 300 (array 300 ℤ) := ⟨λ y, ⟨λ x, power_level sn x y⟩⟩,
  (_,x,y,s) ← check_all arr (arr, arr, arr) 1 none,
  some (to_string x ++ "," ++ to_string y ++ "," ++ to_string s)

end day11
