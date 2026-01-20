
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.

Open Scope Z_scope.

Fixpoint decimal_value (ds : list Z) : Z :=
  match ds with
  | nil => 0
  | d :: ds' => d * Z.pow 10 (Z.of_nat (length ds')) + decimal_value ds'
  end.

Fixpoint list_sum (ds : list Z) : Z :=
  match ds with
  | nil => 0
  | d :: ds' => d + list_sum ds'
  end.

Definition nonempty {A} (l : list A) : Prop :=
  exists x xs, l = x :: xs.

Definition digits_valid (x : Z) (ds : list Z) : Prop :=
  nonempty ds /\
  Forall (fun d => 0 <= d /\ d <= 9) ds /\
  decimal_value ds = Z.abs x /\
  ((x = 0 /\ ds = [0]) \/
   (x <> 0 /\ exists d t, ds = d :: t /\ 1 <= d /\ d <= 9)).

Definition weight_spec (x : Z) (w : Z) : Prop :=
  exists ds,
    digits_valid x ds /\
    ((0 <= x /\ w = list_sum ds) \/
     (x < 0 /\ exists d t, ds = d :: t /\ w = (- d) + list_sum t)).

Definition before {A} (l : list A) (x y : A) : Prop :=
  exists l1 l2 l3, l = l1 ++ x :: l2 ++ y :: l3.

Definition order_by_points_spec (nums : list Z) (res : list Z) : Prop :=
  exists is : list nat,
    Forall (fun i => (i < length nums)%nat) is /\
    Permutation is (seq 0 (length nums)) /\
    Forall2 (fun i x => nth_error nums i = Some x) is res /\
    (forall i j xi xj wi wj,
        before is i j ->
        nth_error nums i = Some xi ->
        nth_error nums j = Some xj ->
        weight_spec xi wi ->
        weight_spec xj wj ->
        wi <= wj /\ (wi = wj -> (i <= j)%nat)).
