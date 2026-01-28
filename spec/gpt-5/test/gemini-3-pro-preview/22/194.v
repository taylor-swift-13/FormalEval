Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Inductive Any : Type :=
| AnyInt : Z -> Any
| AnyStr : string -> Any
| AnyList : list Any -> Any.

Definition int := Z.

Definition IsInt (v : Any) (n : int) : Prop :=
  match v with
  | AnyInt i => i = n
  | _ => False
  end.

Lemma IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.
Proof.
  intros v n m H1 H2. destruct v; simpl in *; try contradiction. subst. reflexivity.
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

Example test_filter_integers_complex : 
  filter_integers_spec 
    [AnyInt 2; 
     AnyList [AnyInt 2; AnyStr "3"]; 
     AnyList [AnyInt 8; AnyInt 5; AnyInt 8; AnyInt 7; AnyInt 6; AnyInt 6]; 
     AnyList [AnyInt 4; AnyInt 4]; 
     AnyList [AnyInt 8; AnyInt 5; AnyInt 8; AnyInt 7; AnyInt 6; AnyInt 6]; 
     AnyList [AnyInt 8; AnyInt 5; AnyInt 8; AnyInt 7; AnyInt 6; AnyInt 6]; 
     AnyList [AnyInt 7; AnyInt 8]; 
     AnyInt 9; 
     AnyInt 1] 
    [2; 9; 1].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 2).
  { simpl. reflexivity. }
  apply fir_cons_nonint.
  { intros n H. simpl in H. contradiction. }
  apply fir_cons_nonint.
  { intros n H. simpl in H. contradiction. }
  apply fir_cons_nonint.
  { intros n H. simpl in H. contradiction. }
  apply fir_cons_nonint.
  { intros n H. simpl in H. contradiction. }
  apply fir_cons_nonint.
  { intros n H. simpl in H. contradiction. }
  apply fir_cons_nonint.
  { intros n H. simpl in H. contradiction. }
  apply fir_cons_int with (n := 9).
  { simpl. reflexivity. }
  apply fir_cons_int with (n := 1).
  { simpl. reflexivity. }
  apply fir_nil.
Qed.