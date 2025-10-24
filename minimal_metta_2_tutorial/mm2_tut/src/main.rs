

mod data;
mod query {
const EX_01:&str = "
(animal cat)
(animal dog)
(animal bird)
(animal human)
(animal spider)

(mammal cat)
(mammal dog)
(mammal human)

(insect spider)

(aves bird)

(feet 4 cat)
(feet 4 dog)
(feet 2 bird)
(feet 2 human)
(feet 8 spider)
";

const EX_02:&str="
(std (boolean (: bool primitive)))
(std (boolean (ctor bool true)))
(std (boolean (ctor bool false)))

(std (boolean (: OR  (-> (. bool bool) bool))))
(std (boolean (= (OR true  true ) true )))
(std (boolean (= (OR false false) true )))
(std (boolean (= (OR false true ) true )))
(std (boolean (= (OR true  false) false)))


(std (boolean (: AND  (-> (. bool bool) bool))))
(std (boolean (= (AND true  true ) true )))
(std (boolean (= (AND false false) false)))
(std (boolean (= (AND false true ) false)))
(std (boolean (= (AND true  false) false)))

(std (boolean (: NOT (-> bool bool))))
(std (boolean (= (NOT true)  false)))
(std (boolean (= (NOT false) true)))
";

}
mod relational_algebra {

}
pub(crate) mod utils;


fn main() {
    println!("Hello, world!");
}


