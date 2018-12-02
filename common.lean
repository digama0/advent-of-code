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
