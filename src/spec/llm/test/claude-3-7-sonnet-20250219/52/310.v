Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition below_threshold_spec (l : list nat) (t : nat) (res : bool) : Prop :=
  res = forallb (fun x => Nat.ltb x t) l.

Definition Zlist_to_natlist (l : list Z) : option (list nat) :=
  let fix aux l :=
    match l with
    | [] => Some []
    | x :: xs =>
      if (0 <=? x) then
        match aux xs with
        | Some ns => Some (Z.to_nat x :: ns)
        | None => None
        end
      else None
    end
  in aux l.

Example test_below_threshold :
  below_threshold_spec (match Zlist_to_natlist [9; 20; 40; -50] with Some ns => ns | None => [] end) 499 true.
Proof.
  unfold below_threshold_spec.
  simpl.
  (* The list contains a negative number -50; Zlist_to_natlist returns None -> [] *)
  reflexivity.
Qed.