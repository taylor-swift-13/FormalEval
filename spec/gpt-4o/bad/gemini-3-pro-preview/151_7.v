Require Import List.
Require Import ZArith.

Open Scope Z_scope.

Definition double_the_difference_spec (lst : list Z) (result : Z) : Prop :=
  result = fold_left (fun acc num =>
    if (Z.odd num && (0 <? num))%bool then acc + num * num else acc) lst 0.

Example test_double_the_difference : double_the_difference_spec 
  [-99%Z; -97%Z; -95%Z; -93%Z; -91%Z; -89%Z; -87%Z; -85%Z; -83%Z; -81%Z; 
   -79%Z; -77%Z; -75%Z; -73%Z; -71%Z; -69%Z; -67%Z; -65%Z; -63%Z; -61%Z; 
   -59%Z; -57%Z; -55%Z; -53%Z; -51%Z; -49%Z; -47%Z; -45%Z; -43%Z; -41%Z; 
   -39%Z; -37%Z; -35%Z; -33%Z; -31%Z; -29%Z; -27%Z; -25%Z; -23%Z; -21%Z; 
   -19%Z; -17%Z; -15%Z; -13%Z; -11%Z; -9%Z; -7%Z; -5%Z; -3%Z; -1%Z; 
   1%Z; 3%Z; 5%Z; 7%Z; 9%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 
   21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 31%Z; 33%Z; 35%Z; 37%Z; 39%Z; 
   41%Z; 43%Z; 45%Z; 47%Z; 49%Z; 51%Z; 53%Z; 55%Z; 57%Z; 59%Z; 
   61%Z; 63%Z; 65%Z; 67%Z; 69%Z; 71%Z; 73%Z; 75%Z; 77%Z; 79%Z; 
   81%Z; 83%Z; 85%Z; 87%Z; 89%Z; 91%Z; 93%Z; 95%Z; 97%Z; 99%Z] 
  166650%Z.
Proof.
  unfold double_the_difference_spec.
  vm_compute.
  reflexivity.
Qed.