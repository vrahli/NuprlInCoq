Axiom FunctionalChoice_on :
  forall (A B : Type) (R : A -> B -> Prop),
    (forall a : A, exists (b : B), R a b)
    -> (exists (f : A -> B), forall a : A, R a (f a)).

Axiom DependentFunctionalChoice_on :
  forall (A:Type) (B:A -> Type) (R:forall x:A, B x -> Prop),
    (forall x:A, exists y : B x, R x y) ->
    (exists f : (forall x:A, B x), forall x:A, R x (f x)).
