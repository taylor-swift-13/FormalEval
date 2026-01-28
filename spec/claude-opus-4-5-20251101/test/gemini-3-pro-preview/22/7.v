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

(* Test case: input = [[1%Z; "2"; "3"; 4%Z; -5%Z]], output = [1%Z; 4%Z; -5%Z] *)
Example test_filter_integers_mixed : filter_integers_spec [PyInt 1; PyString; PyString; PyInt 4; PyInt (-5)] [1; 4; -5]%Z.
Proof.
  unfold filter_integers_spec.
  split.
  - simpl. reflexivity.
  - intros z.
    split.
    + intros H.
      simpl in H.
      destruct H as [H1 | [H2 | [H3 | H4]]].
      * subst. exists (PyInt 1). split; [simpl; auto | reflexivity].
      * subst. exists (PyInt 4). split; [simpl; auto 10 | reflexivity].
      * subst. exists (PyInt (-5)). split; [simpl; auto 10 | reflexivity].
      * contradiction.
    + intros [v [H_in H_eq]].
      subst v.
      simpl in H_in.
      destruct H_in as [H1 | [H2 | [H3 | [H4 | [H5 | H6]]]]]; try discriminate.
      * inversion H1. subst. simpl. left. reflexivity.
      * inversion H4. subst. simpl. right. left. reflexivity.
      * inversion H5. subst. simpl. right. right. left. reflexivity.
      * contradiction.
Qed.