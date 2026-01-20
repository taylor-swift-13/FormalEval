Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Definition nl := String (ascii_of_nat 10) "".

Example test_concatenate_newlines : concatenate_spec 
  [ "hello" ++ nl ++ "world";
    "this" ++ nl ++ "string" ++ nl ++ "has" ++ nl ++ "multiple" ++ nl ++ "newlines";
    "jumps";
    "this" ++ nl ++ "string" ++ nl ++ "has" ++ nl ++ "multipule" ++ nl ++ "newlines";
    "hello" ++ nl ++ "world";
    "aa";
    "this" ++ nl ++ "string" ++ nl ++ "has" ++ nl ++ "mulntiple" ++ nl ++ "newlines" ]
  ("hello" ++ nl ++ "world" ++ 
   "this" ++ nl ++ "string" ++ nl ++ "has" ++ nl ++ "multiple" ++ nl ++ "newlines" ++ 
   "jumps" ++ 
   "this" ++ nl ++ "string" ++ nl ++ "has" ++ nl ++ "multipule" ++ nl ++ "newlines" ++ 
   "hello" ++ nl ++ "world" ++ 
   "aa" ++ 
   "this" ++ nl ++ "string" ++ nl ++ "has" ++ nl ++ "mulntiple" ++ nl ++ "newlines").
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.