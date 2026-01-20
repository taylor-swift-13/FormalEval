Require Import List.
Require Import ZArith.

Import ListNotations.

Inductive PyValue : Type :=
  | PyInt : Z -> PyValue
  | PyFloat : PyValue
  | PyString : PyValue
  | PyDict : PyValue
  | PyList : PyValue
  | PyOther : PyValue.

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

Example test_mixed_list : filter_integers_spec 
  [PyOther; PyOther; PyOther; PyInt 0; PyInt (-10); PyString; PyList; PyDict; PyFloat] 
  [0%Z; (-10)%Z].
Proof.
  unfold filter_integers_spec.
  split.
  - simpl. reflexivity.
  - intros z. split.
    + simpl. intros [H | [H | H]].
      * exists (PyInt 0). split; [right; right; right; left; reflexivity | congruence].
      * exists (PyInt (-10)). split; [right; right; right; right; left; reflexivity | congruence].
      * contradiction.
    + intros [v [Hv Heq]].
      simpl in Hv.
      destruct Hv as [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]].
      * subst v. discriminate.
      * subst v. discriminate.
      * subst v. discriminate.
      * subst v. injection Heq as Heq. left. exact Heq.
      * subst v. injection Heq as Heq. right. left. exact Heq.
      * subst v. discriminate.
      * subst v. discriminate.
      * subst v. discriminate.
      * subst v. discriminate.
      * contradiction.
Qed.