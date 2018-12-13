-- https://adventofcode.com/2018/day/10

import .common data.list.basic algebra.pi_instances
open parser

namespace day10

def signed_number' : parser ℤ :=
ch ' ' >> (int.of_nat <$> number) <|>
ch '-' >> ((λ x:ℕ, -x) <$> number)

def pair : parser (ℤ × ℤ) := prod.mk <$>
 (ch '<' *> signed_number') <*>
 (str ", " *> signed_number' <* ch '>')

def day10 := go "day10.txt" $ many $
  prod.mk <$> (str "position=" *> pair) <*>
    (str " velocity=" *> pair <* ch '\n')

-- argmin_t len^2 sum_i (xi - avg)^2
-- = argmin_t sum_i ((len * vi - sumv)*t + (len*xi - sum))^2
-- argmin_t sum_i (ai*t + bi) = - sum_i (ai*bi) / sum_i ai^2
def cluster_time (es : list ((ℤ × ℤ) × ℤ × ℤ)) : ℤ :=
let len : ℤ := es.length,
    (sum, sumv) := list.sum es,
    (bs, as) := (list.map (λ e, ((len,len),len,len) * e - (sum, sumv)) es).unzip,
    as' := as.unzip.1 ++ as.unzip.2,
    bs' := bs.unzip.1 ++ bs.unzip.2 in
-list.sum (list.zip_with (*) as' bs') / list.sum (as'.map (λ x, x*x))

def bbox1 : option (ℤ × ℤ × ℤ × ℤ) → ℤ × ℤ → option (ℤ × ℤ × ℤ × ℤ)
| none (x, y) := (x, x, y, y)
| (some (l, r, t, b)) (x, y) :=
  some (min l x, max r x, min t y, max b y)

#eval day10 $ λ es, do
  let tm := cluster_time es,
  let es' := es.map (λ ⟨p, v⟩, v * tm + p),
  (l, r, t, b) ← es'.foldl bbox1 none,
  let w := int.to_nat (r - l + 1),
  let h := int.to_nat (b - t + 1),
  let arr : array h (array w bool) := es'.foldl (λ a xy,
    array.modify' (int.to_nat (xy.2 - t))
      (λ a, array.write' a (int.to_nat (xy.1 - l)) tt) a)
    ⟨λ _, ⟨λ _, ff⟩⟩,
  let str : string := array.iterate arr "" $
    λ i a s, string.push (array.iterate a s $
      λ j b s, s.push (cond b '#' ' ')) '\n',
  trace (to_string tm) (some str)

-- 10645 (part 2)

-- ######  #####   #    #  ######   ####   #    #     ###     ###
-- #       #    #  #   #   #       #    #  #   #       #       #
-- #       #    #  #  #    #       #       #  #        #       #
-- #       #    #  # #     #       #       # #         #       #
-- #####   #####   ##      #####   #       ##          #       #
-- #       #  #    ##      #       #       ##          #       #
-- #       #   #   # #     #       #       # #         #       #
-- #       #   #   #  #    #       #       #  #    #   #   #   #
-- #       #    #  #   #   #       #    #  #   #   #   #   #   #
-- ######  #    #  #    #  ######   ####   #    #   ###     ###   (part 1)

end day10
