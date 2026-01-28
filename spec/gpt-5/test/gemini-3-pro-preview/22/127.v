Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Inductive Any : Type :=
| Any_int : Z -> Any
| Any_str : string -> Any
| Any_list : list Any -> Any.

Definition int := Z.

Definition IsInt (v : Any) (n : int) : Prop :=
  match v with
  | Any_int i => i = n
  | _ => False
  end.

Lemma IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.
Proof.
  intros v n m Hn Hm.
  destruct v; simpl in *; try contradiction.
  subst. reflexivity.
Qed.

Inductive filter_integers_rel : list Any -> list int -> Prop :=
| fir_nil : filter_integers_rel [] []
| fir_cons_int v n vs res :
    IsInt v n ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) (n :: res)
| fir_cons_nonint v vs res :
    (forall n, ~ IsInt v n) ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) res.

Definition filter_integers_spec (values : list Any) (res : list int) : Prop :=
  filter_integers_rel values res.

Example test_filter_integers : 
  filter_integers_spec 
    [Any_int 1; Any_int 10; Any_list [Any_int 2; Any_str "3"]; Any_list [Any_int 4]; Any_list [Any_int 5; Any_int 6]; Any_list [Any_int 7; Any_int 2]; Any_list [Any_int 7; Any_int 2]; Any_int 9] 
    [1; 10; 9].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1). { simpl. reflexivity. }
  apply fir_cons_int with (n := 10). { simpl. reflexivity. }
  apply fir_cons_nonint. { intros n H. simpl in H. contradiction. }
  apply fir_cons_nonint. { intros n H. simpl in H. contradiction. }
  apply fir_cons_nonint. { intros n H. simpl in H. contradiction. }
  apply fir_cons_nonint. { intros n H. simpl in H. contradiction. }
  apply fir_cons_nonint. { intros n H. simpl in H. contradiction. }
  apply fir_cons_int with (n := 9). { simpl. reflexivity. }
  apply fir_nil.
Qed.