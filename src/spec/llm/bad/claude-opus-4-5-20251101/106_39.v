Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Fixpoint factorial (n : nat) : Z :=
  match n with
  | O => 1
  | S n' => Z.of_nat n * factorial n'
  end.

Fixpoint sum_1_to_n (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => Z.of_nat n + sum_1_to_n n'
  end.

Definition f_element (i : nat) : Z :=
  if Nat.even i then factorial i
  else sum_1_to_n i.

Fixpoint f_list (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => f_list n' ++ [f_element n]
  end.

Definition f_spec (n : nat) (result : list Z) : Prop :=
  result = f_list n /\
  length result = n /\
  forall i : nat, (1 <= i <= n)%nat ->
    nth (i - 1) result 0 = f_element i.

Lemma f_list_length : forall n, length (f_list n) = n.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite app_length. simpl. rewrite IHn. lia.
Qed.

Lemma nth_app_right : forall (A : Type) (l1 l2 : list A) (d : A) (n : nat),
  n = length l1 -> nth n (l1 ++ l2) d = nth 0 l2 d.
Proof.
  intros A l1 l2 d n Hlen.
  subst n.
  rewrite app_nth2.
  - rewrite Nat.sub_diag. reflexivity.
  - lia.
Qed.

Lemma nth_app_left : forall (A : Type) (l1 l2 : list A) (d : A) (n : nat),
  (n < length l1)%nat -> nth n (l1 ++ l2) d = nth n l1 d.
Proof.
  intros A l1 l2 d n Hlt.
  apply app_nth1. exact Hlt.
Qed.

Lemma f_list_nth : forall n i, (1 <= i <= n)%nat -> nth (i - 1) (f_list n) 0 = f_element i.
Proof.
  induction n.
  - intros i H. lia.
  - intros i H.
    simpl.
    destruct (Nat.eq_dec i (S n)).
    + subst i.
      rewrite nth_app_right with (l2 := [f_element (S n)]).
      * simpl. reflexivity.
      * rewrite f_list_length. lia.
    + assert (Hi : (1 <= i <= n)%nat) by lia.
      rewrite nth_app_left.
      * apply IHn. exact Hi.
      * rewrite f_list_length. lia.
Qed.

Definition expected_output_54 : list Z :=
  [1; 2; 6; 24; 15; 720; 28; 40320; 45; 3628800; 66; 479001600; 91; 87178291200; 120; 20922789888000; 153; 6402373705728000; 190; 2432902008176640000; 231; 1124000727777607680000; 276; 620448401733239439360000; 325; 403291461126605635584000000; 378; 304888344611713860501504000000; 435; 265252859812191058636308480000000; 496; 263130836933693530167218012160000000; 561; 295232799039604140847618609643520000000; 630; 371993326789901217467999448150835200000000; 703; 523022617466601111760007224100074291200000000; 780; 815915283247897734345611269596115894272000000000; 861; 1405006117752879898543142606244511569936384000000000; 946; 2658271574788448768043625811014615890319638528000000000; 1035; 5502622159812088949850305428800254892961651752960000000000; 1128; 12413915592536072670862289047373375038521486354677760000000000; 1225; 30414093201713378043612608166064768844377641568960512000000000000; 1326; 80658175170943878571660636856403766975289505440883277824000000000000; 1431; 230843697339241380472092742683027581083278564571807941132288000000000000].

Lemma test_f_list_54_eq : f_list 54 = expected_output_54.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example test_f_spec_54 : f_spec 54 expected_output_54.
Proof.
  unfold f_spec.
  split.
  - exact test_f_list_54_eq.
  - split.
    + vm_compute. reflexivity.
    + intros i Hi.
      rewrite test_f_list_54_eq.
      symmetry. rewrite <- test_f_list_54_eq.
      apply f_list_nth.
      exact Hi.
Qed.