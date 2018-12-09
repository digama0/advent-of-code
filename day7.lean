-- https://adventofcode.com/2018/day/7

import .common data.nat.dist data.option
open parser

namespace day7

def day7 := go "day7.txt" $ many $
  prod.mk <$> (str "Step " *> Letter <* str " must be finished before step ") <*> Letter <* str " can begin.\n"

def add_deps : rbtree char × rbmap char (ℕ × rbtree char) →
  char × char → rbtree char × rbmap char (ℕ × rbtree char)
| (s, m) (a, b) := ((s.insert a).insert b,
  m.modify b (1, (mk_rbtree _).insert a) (λ ⟨n, t⟩, (n+1, t.insert a)))

def find1 (m : rbmap char (ℕ × rbtree char)) (c : char) : option char :=
if ∀ i ∈ m.find c, prod.fst i = 0 then some c else none

def find (verts : list char) (m : rbmap char (ℕ × rbtree char)) :=
verts.foldl (λ (r : option char) c, r <|> find1 m c) none

def process : ℕ → list char → string →
  rbmap char (ℕ × rbtree char) → option string
| 0     verts s m := some s
| (n+1) verts s m := do
  best ← find verts m,
  process n (verts.erase best) (s.push best)
    (m.fold (λ a ⟨n, b⟩ m',
      if b.contains best then m'.insert a (n-1, b) else m') m)

#eval day7 $ λ es, do
  let (verts, deps) := es.foldl add_deps (mk_rbtree _, mk_rbmap _ _),
  process verts.size verts.to_list "" deps

def time (c : char) : ℕ := c.to_nat - 'A'.to_nat + 61

def next {n} (tm : ℕ) (ready : bool) (i : fin n) : option (ℕ × char) →
  option (fin n × ℕ × option char) → option (fin n × ℕ × option char)
| none none := if ready then some (i, tm, none) else none
| (some (t, c)) none := some (i, t, some c)
| none (some (j, t', c')) :=
  if ready ∧ tm < t' then some (i, tm, none) else some (j, t', c')
| (some (t, c)) (some (j, t', c')) :=
  if t < t' then some (i, t, c) else some (j, t', c')

def process2 : ℕ → ℕ → array 5 (option (ℕ × char)) → list char → string →
  rbmap char (ℕ × rbtree char) → option ℕ
| 0     tm work verts s m := none
| (n+1) tm work [] s m :=
  work.iterate tm (λ _ n, option.lift_or_get max (n.map prod.fst))
| (n+1) tm work verts s m := do
  let new := find verts m,
  (i, t, old) ← work.iterate none (next tm new.is_some),
  let (s', m', new') := (match old with
  | none := (s, m, new)
  | (some old) :=
    let m' : rbmap char (ℕ × rbtree char) :=
      m.fold (λ a ⟨n, b⟩ m',
        if b.contains old then m'.insert a (n-1, b) else m') m in
    (s.push old, m', find verts m')
  end : _ × _ × _),
  match new' with
  | none := process2 n t (work.write i none) verts s' m'
  | (some new'') := process2 n t
    (work.write i (some (t + time new'', new''))) (verts.erase new'') s' m'
  end

#eval day7 $ λ es, do
  let (verts, deps) := es.foldl add_deps (mk_rbtree _, mk_rbmap _ _),
  to_string <$> process2 (2*verts.size) 0 ⟨λ _, none⟩ verts.to_list "" deps

end day7
