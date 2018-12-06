-- https://adventofcode.com/2018/day/6

import .common data.list.basic data.nat.dist data.option
open parser

namespace day6

def day6 := go "day6.txt" $ many $
  prod.mk <$> (number <* str ", ") <*> number <* ch '\n'

def bbox1 : option (ℕ × ℕ × ℕ × ℕ) → ℕ × ℕ → option (ℕ × ℕ × ℕ × ℕ)
| none (x, y) := (x, x, y, y)
| (some (l, r, t, b)) (x, y) :=
  some (min l x, max r x, min t y, max b y)

def iter {α} (f : ℕ → α → α) : ℕ → ℕ → α → α
| x 0     a := a
| x (m+1) a := iter (x+1) m (f x a)

def iter2 {α} (f : ℕ → ℕ → α → α) (x m : ℕ) : ℕ → ℕ → α → α :=
iter (λ y, iter (λ x, f x y) x m)

inductive result (n : ℕ) : Type
| none {} : result
| one (i : fin n) : ℕ → result
| many {} : ℕ → result

def result.min {n} : result n → fin n → ℕ → result n
| result.none i a := result.one i a
| (result.many b) i a :=
  if a < b then result.one i a else result.many b
| (result.one j b) i a :=
  if a < b then result.one i a else
  if a = b then result.many b else result.one j b

def dist (x₁ y₁ x₂ y₂ : ℕ) := nat.dist x₁ x₂ + nat.dist y₁ y₂

def min1 {n} (x₁ y₁ : ℕ) (i : fin n) : ℕ × ℕ → result n → result n
| (x₂, y₂) r := result.min r i (dist x₁ y₁ x₂ y₂)

def step {n} (l r t b : ℕ) (locs : array n (ℕ × ℕ)) (x y : ℕ) (a : array n (option ℕ)) : array n (option ℕ) :=
match locs.iterate result.none (min1 x y) with
| result.one i _ :=
  if x = l ∨ x = r ∨ y = t ∨ y = b then
    a.write i none
  else a.modify i (option.map (+1))
| _ := a
end

#eval day6 $ λ es, do
  (l, r, t, b) ← es.foldl bbox1 none,
  let w := r - l + 1,
  let h := b - t + 1,
  let ⟨n, locs⟩ := es.to_buffer,
  let s0 : array n (option ℕ) := ⟨λ _, some 0⟩,
  let st := iter2 (step l r t b locs) l w t h s0,
  let res := st.iterate none (λ _, option.lift_or_get max),
  to_string <$> res

def step2 {n} (locs : array n (ℕ × ℕ)) (x y : ℕ) (i : ℕ) : ℕ :=
if locs.iterate 0 (λ _ ⟨x', y'⟩, (+ dist x y x' y')) < 10000 then i + 1 else i

#eval day6 $ λ es, do
  (l, r, t, b) ← es.foldl bbox1 none,
  let w := r - l + 1,
  let h := b - t + 1,
  let ⟨n, locs⟩ := es.to_buffer,
  let res := iter2 (step2 locs) l w t h 0,
  to_string res

end day6
