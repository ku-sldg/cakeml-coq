datatype nat = O
             | S nat

fun plus x y = case x of
                  O => y
                | S xp => S (plus xp y)

val two = S (S O)
val three = S two

val answer = plus two three
