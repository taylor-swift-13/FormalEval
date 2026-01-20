Require Import List.
Require Import ZArith.

Import ListNotations.

Inductive PyValue : Type :=
  | PyInt : Z -> PyValue
  | PyFloat : PyValue
  | PyString : PyValue
  | PyDict : PyValue
  | PyList : PyValue
  | PyOther : PyValue
  | PyBool : bool -> PyValue
  | PyNone : PyValue.

Definition is_integer (v : PyValue) : bool :=
  match v with
  | PyInt _ => true
  | _ => false
  end.

Definition get_int (v : PyValue) : option Z :=
  match v with
  | PyInt n => Some n
  | _ => None
  end.

Fixpoint filter_integers_impl (values : list PyValue) : list Z :=
  match values with
  | [] => []
  | (PyInt n) :: rest => n :: filter_integers_impl rest
  | _ :: rest => filter_integers_impl rest
  end.

Definition filter_integers_spec (values : list PyValue) (result : list Z) : Prop :=
  result = filter_integers_impl values /\
  (forall z, In z result <-> exists v, In v values /\ v = PyInt z).

Definition test_input : list PyValue :=
  [PyBool true; PyBool false; PyNone; PyInt 0%Z; PyInt (-10)%Z; PyString; PyList; PyDict; PyFloat].

Example test_mixed_list : filter_integers_spec test_input [0%Z; (-10)%Z].
Proof.
  unfold filter_integers_spec, test_input.
  split.
  - simpl. reflexivity.
  - intros z. split.
    + simpl. intros [H | [H | H]].
      * exists (PyInt 0%Z). split; [right; right; right; left; reflexivity | congruence].
      * exists (PyInt (-10)%Z). split; [right; right; right; right; left; reflexivity | congruence].
      * contradiction.
    + intros [v [Hv Heq]].
      simpl in Hv.
      destruct Hv as [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]].
      * subst v. discriminate.
      * subst v. discriminate.
      * subst v. discriminate.
      * subst v. injection Heq as Heq. simpl. left. assumption.
      * subst v. injection Heq as Heq. simpl. right. left. assumption.
      * subst v. discriminate.
      * subst v. discriminate.
      * subst v. discriminate.
      * subst v. discriminate.
      * contradiction.
Qed.