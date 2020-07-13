datatype nat = O
             | S nat

val succ = fn x => S x

fun plus x y = case x of
                   O => y
                | S xp => S (plus xp y)

fun plus2 x y = case x of
                   O => y
                 | S xp => succ (plus xp y)

fun mult x y = case x of
                   O => O
                 | S xp => let val z = mult xp y in plus y z end

exception SubtrahendLargerThanMinuend

fun minus x y = case y of
                    O => x
                  | S yp => (case x of
                                O => raise SubtrahendLargerThanMinuend
                              | S xp => (minus xp yp))


fun abs_minus x y = (minus x y) handle SubtrahendLargerThanMinuend => minus y x

val two = S (S O)
val three = S two

val answer = plus two three
