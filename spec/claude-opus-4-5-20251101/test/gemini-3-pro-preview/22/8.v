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

Example test_filter_integers_mixed : filter_integers_spec 
  [PyInt 1000000%Z; PyInt (-1000000)%Z; PyFloat; PyString; PyString; PyList] 
  [1000000%Z; (-1000000)%Z].
Proof.
  unfold filter_integers_spec.
  split.
  - simpl. reflexivity.
  - intros z.
    split.
    + intros H.
      simpl in H.
      destruct H as [H | [H | H]].
      * subst z. exists (PyInt 1000000%Z). split.
        -- simpl. left. reflexivity.
        -- reflexivity.
      * subst z. exists (PyInt (-1000000)%Z). split.
        -- simpl. right. left. reflexivity.
        -- reflexivity.
      * contradiction.
    + intros [v [H_in H_eq]].
      subst v.
      simpl in H_in.
      destruct H_in as [H | [H | [H | [H | [H | [H | H]]]]]].
      * inversion H. subst. simpl. left. reflexivity.
      * inversion H. subst. simpl. right. left. reflexivity.
      * discriminate H.
      * discriminate H.
      * discriminate H.
      * discriminate H.
      * contradiction.
Qed.