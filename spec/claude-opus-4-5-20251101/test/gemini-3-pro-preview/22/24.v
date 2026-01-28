Require Import List.
Require Import ZArith.

Import ListNotations.
Open Scope Z_scope.

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

Example test_filter_integers_complex : 
  filter_integers_spec 
    [PyOther; PyOther; PyOther; PyInt 0; PyInt (-10); PyString; PyList; PyDict; PyFloat] 
    [0; -10].
Proof.
  unfold filter_integers_spec.
  split.
  - simpl. reflexivity.
  - intros z. split.
    + intros H.
      simpl in H.
      destruct H as [H | [H | H]]; try contradiction; subst.
      * exists (PyInt 0). split; [| reflexivity].
        simpl. right. right. right. left. reflexivity.
      * exists (PyInt (-10)). split; [| reflexivity].
        simpl. right. right. right. right. left. reflexivity.
    + intros [v [H_in H_eq]].
      subst v.
      simpl in H_in.
      destruct H_in as [H | H]; [discriminate H |].
      destruct H as [H | H]; [discriminate H |].
      destruct H as [H | H]; [discriminate H |].
      destruct H as [H | H].
      * injection H as Hz. subst z. simpl. left. reflexivity.
      * destruct H as [H | H].
        -- injection H as Hz. subst z. simpl. right. left. reflexivity.
        -- destruct H as [H | H]; [discriminate H |].
           destruct H as [H | H]; [discriminate H |].
           destruct H as [H | H]; [discriminate H |].
           destruct H as [H | H]; [discriminate H |].
           contradiction.
Qed.