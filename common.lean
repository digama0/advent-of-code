import system.io data.buffer.parser
open parser

def number : parser ℕ :=
string.to_nat <$> many_char1 (sat $ λ c,
  '0'.to_nat ≤ c.to_nat ∧ c.to_nat ≤ '9'.to_nat)

def signed_number : parser ℤ :=
ch '+' >> (int.of_nat <$> number) <|>
ch '-' >> ((λ x:ℕ, -x) <$> number)

def letter : parser char :=
sat (λ c, 'a'.to_nat ≤ c.to_nat ∧ c.to_nat ≤ 'z'.to_nat)

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
