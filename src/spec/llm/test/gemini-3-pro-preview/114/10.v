Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sum (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => h + sum t
  end.

Fixpoint prefixes (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | x :: xs => [x] :: map (cons x) (prefixes xs)
  end.

Fixpoint suffixes (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | x :: xs => (x :: xs) :: suffixes xs
  end.

Definition sublists (l : list Z) : list (list Z) :=
  flat_map prefixes (suffixes l).

Fixpoint min_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs =>
    match xs with
    | [] => x
    | _ => Z.min x (min_list xs)
    end
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  min_list (map sum (sublists nums)).

Example minSubArraySum_example : minSubArraySum [-10] = -10.
Proof.
  compute.
  reflexivity.
Qed.