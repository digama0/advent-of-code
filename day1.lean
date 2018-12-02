import .common data.list.basic
open parser sum

def day1 := go "day1.txt" (many (signed_number <* ch '\n'))

namespace day1

#eval day1 $ λ l, to_string l.sum -- 427

/- non meta with a depth limiter -/
def iter (inp : list ℤ) : ℕ → list ℤ → rbmap ℤ unit → ℤ → option string
| 0 _ _ _ := none
| (n+1) [] s z := iter n inp s z
| (n+1) (i::l) s z :=
  let j := i + z in
  if s.contains j then
    some (to_string j)
  else iter (n+1) l (s.insert j ()) j

-- #eval day1 $ λ l, iter l 139 [] (mk_rbmap _ _) 0 -- 341

/- no depth limiter -/
meta def iter2 (inp : list ℤ) : list ℤ → rbmap ℤ unit → ℤ → string
| [] s z := iter2 inp s z
| (i::l) s z :=
  let j := i + z in
  if s.contains j then to_string j
  else iter2 l (s.insert j ()) j

-- #eval day1 $ λ l, iter2 l [] (mk_rbmap _ _) 0 -- 341

/- A smarter algorithm that looks ahead to find out if and how many
  times it will loop before reporting an answer, and skips the whole thing.
  The advantage is that it is much faster, non-meta, with no depth limiter,
  and reports failure rather than nontermination -/

def insert_divmod (pd : ℤ)
  (s : rbmap ℤ (rbmap ℤ unit)) (n : ℤ) : ℤ ⊕ rbmap ℤ (rbmap ℤ unit) :=
let ret (c : rbmap ℤ unit) : ℤ ⊕ rbmap ℤ (rbmap ℤ unit) :=
  sum.inr (s.insert (n % pd) (c.insert (n / pd) ())) in
match s.find (n % pd) with
| none := ret (mk_rbmap ℤ _)
| (some c) := if c.contains (n / pd) then sum.inl n else ret c
end

def rbmap.map {α β γ lt} [decidable_rel lt]
  (f : α → β → γ) (s : rbmap α β lt) : rbmap α γ lt :=
s.fold (λ a b c, c.insert a (f a b)) (mk_rbmap α γ lt)

def convolve1 (cur : ℤ) : option (ℤ × rbmap ℤ (with_top ℤ)) → option (ℤ × rbmap ℤ (with_top ℤ))
| none := some (cur, mk_rbmap ℤ _)
| (some (prev, s)) := some (cur, s.insert prev (some (cur - prev)))

def convolve (s : rbmap ℤ unit) : rbmap ℤ (with_top ℤ) :=
match s.fold (λ cur _, convolve1 cur) none with
| none := mk_rbmap _ _
| (some (n, s)) := s.insert n ⊤
end

def scanl' {α β} (f : α → β → α) : α → list β → α × list α
| a []     := (a, [])
| a (b::l) := let (a', l') := scanl' (f a b) l in (a', a :: l')

def min1 (conv : rbmap ℤ (rbmap ℤ (with_top ℤ))) (pd : ℤ) :
  with_top ℤ × ℤ → ℤ → with_top ℤ × ℤ
| (v, old) n := option.get_or_else (do
    c ← conv.find (n % pd),
    v' ← c.find (n / pd),
    d ← v',
    guard (v' < v) $> (v', n + d * pd))
  (v, old)

def find_dup (inp : list ℤ) : option ℤ := do
  let (pd, accum) := scanl' (+) 0 inp,
  match accum.mfoldl (insert_divmod pd) (mk_rbmap ℤ _) with
  | sum.inl res := res
  | sum.inr s :=
    if pd = 0 then some 0 else
    let conv := rbmap.map (λ _, convolve) s,
        (v, res) := accum.foldl (min1 conv pd) (⊤, 0) in
    res <$ v
  end

#eval day1 $ λ inp, to_string <$> find_dup inp -- 341

end day1
