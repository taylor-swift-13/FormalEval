Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint solution (l : list Z) : list Z :=
  match l with
  | [] => [0; 0]
  | x :: xs =>
    if x =? 0 then [0; 0]
    else
      match solution xs with
      | [e; o] => if Z.even x then [e + 1; o] else [e; o + 1]
      | _ => [0; 0]
      end
  end.

Example test_case: solution [0; 2; 4; 6; 8; 10; 3; 5; 9; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 31; 33; 9; 35; 39; 39; 25] = [0; 0].
Proof.
  simpl.
  reflexivity.
Qed.