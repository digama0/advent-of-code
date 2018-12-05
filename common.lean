import system.io data.buffer.parser
open parser

def number : parser ℕ :=
string.to_nat <$> many_char1 (sat char.is_digit)

def signed_number : parser ℤ :=
ch '+' >> (int.of_nat <$> number) <|>
ch '-' >> ((λ x:ℕ, -x) <$> number)

def letter : parser char := sat char.is_lower

def go {α} (file : string) (p : parser α) (m : α → option string) : io unit :=
do s ← io.fs.read_file file,
  sum.inr a ← return $ run p s,
  some str ← return $ m a,
  trace str (return ())

def test {α} (inp : string) (p : parser α) (m : α → option string) : io unit :=
do sum.inr a ← return $ run p inp.to_char_buffer,
  some str ← return $ m a,
  trace str (return ())

def rbmap.modify {α β lt} [decidable_rel lt] (s : rbmap α β lt)
  (a : α) (z : β) (f : β → β) : rbmap α β lt :=
s.insert a $ match s.find a with
| (some b) := f b
| none := z
end

def modify_many {n α} (f : α → α) : ℕ → ℕ → array n α → array n α
| s 0     a := a
| s (i+1) a := if h : s < n then
    let a' := a.write ⟨s, h⟩ (f (a.read ⟨s, h⟩)) in
    modify_many (s+1) i a'
  else a
