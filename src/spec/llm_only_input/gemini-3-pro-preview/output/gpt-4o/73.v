Require Import List.
Require Import Arith.
Require Import Nat.
Import ListNotations.

Definition smallest_change_spec (arr : list nat) (cnt : nat) : Prop :=
  let arr_reversed := rev arr in
  cnt = fold_left (fun acc i =>
    if nth i arr 0 =? nth i arr_reversed 0 then acc else acc + 1)
    (seq 0 (length arr / 2)) 0.

Example test_smallest_change : smallest_change_spec [1; 2; 3; 5; 4; 7; 9; 6] 4.
Proof.
  (* Unfold the definition to expose the computation *)
  unfold smallest_change_spec.
  
  (* Since all values are concrete constants, we can reduce the term 
     entirely using reflexivity. 
     
     Step-by-step reduction logic (implicitly handled by reflexivity):
     1. length arr = 8, so length arr / 2 = 4.
     2. seq 0 4 = [0; 1; 2; 3].
     3. arr_reversed = [6; 9; 7; 4; 5; 3; 2; 1].
     4. The fold_left iterates i from 0 to 3:
        - i=0: arr[0]=1, rev[0]=6. 1 <> 6, acc becomes 0+1 = 1.
        - i=1: arr[1]=2, rev[1]=9. 2 <> 9, acc becomes 1+1 = 2.
        - i=2: arr[2]=3, rev[2]=7. 3 <> 7, acc becomes 2+1 = 3.
        - i=3: arr[3]=5, rev[3]=4. 5 <> 4, acc becomes 3+1 = 4.
     5. Final result is 4.
     6. 4 = 4 is True.
  *)
  reflexivity.
Qed.