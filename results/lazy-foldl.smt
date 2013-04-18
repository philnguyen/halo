; foldl  ∈  (CF CF -> CF) CF CF -> CF
(declare-sort T)
(declare-fun f-foldr1 (T T) T)
(declare-fun rec-foldr1 (T T) T)
(declare-const ptr-foldr1 T)
(declare-const ptr-rec-foldr1 T)
(declare-fun f-tail (T) T)
(declare-fun rec-tail (T) T)
(declare-const ptr-tail T)
(declare-const ptr-rec-tail T)
(declare-fun f-head (T) T)
(declare-fun rec-head (T) T)
(declare-const ptr-head T)
(declare-const ptr-rec-head T)
(declare-fun f-cons-eta (T T) T)
(declare-fun rec-cons-eta (T T) T)
(declare-const ptr-cons-eta T)
(declare-const ptr-rec-cons-eta T)
(declare-fun f-reverse (T) T)
(declare-fun rec-reverse (T) T)
(declare-const ptr-reverse T)
(declare-const ptr-rec-reverse T)
(declare-fun f-map-foldr-step (T T T) T)
(declare-fun rec-map-foldr-step (T T T) T)
(declare-const ptr-map-foldr-step T)
(declare-const ptr-rec-map-foldr-step T)
(declare-fun f-map (T T) T)
(declare-fun rec-map (T T) T)
(declare-const ptr-map T)
(declare-const ptr-rec-map T)
(declare-fun f-foldl (T T T) T)
(declare-fun rec-foldl (T T T) T)
(declare-const ptr-foldl T)
(declare-const ptr-rec-foldl T)
(declare-fun f-foldr (T T T) T)
(declare-fun rec-foldr (T T T) T)
(declare-const ptr-foldr T)
(declare-const ptr-rec-foldr T)
(declare-fun f-cons? (T) T)
(declare-fun rec-cons? (T) T)
(declare-const ptr-cons? T)
(declare-const ptr-rec-cons? T)
(declare-const k-True T)
(declare-const k-False T)
(declare-fun k-Cons (T T) T)
(declare-const k-Nil T)
(declare-const k-Zero T)
(declare-fun k-Succ (T) T)
(declare-fun sel-0-Cons (T) T)
(declare-fun sel-1-Cons (T) T)
(declare-fun sel-0-Succ (T) T)
(declare-fun app (T T) T)
(declare-const unr T)
(declare-const bad T)
(declare-fun cf (T) Bool)
(assert (forall ((x T)) (= (app bad x) bad)))
(assert (forall ((x T)) (= (app unr x) unr)))
(assert (distinct bad unr))
(assert (distinct k-True k-False))
(assert (forall ((y1 T) (y2 T)) (distinct k-True (k-Cons y1 y2))))
(assert (distinct k-True k-Nil))
(assert (distinct k-True k-Zero))
(assert (forall ((y1 T)) (distinct k-True (k-Succ y1))))
(assert (distinct k-False k-True))
(assert (forall ((y1 T) (y2 T)) (distinct k-False (k-Cons y1 y2))))
(assert (distinct k-False k-Nil))
(assert (distinct k-False k-Zero))
(assert (forall ((y1 T)) (distinct k-False (k-Succ y1))))
(assert (forall ((x1 T) (x2 T)) (distinct (k-Cons x1 x2) k-True)))
(assert (forall ((x1 T) (x2 T)) (distinct (k-Cons x1 x2) k-False)))
(assert (forall ((x1 T) (x2 T)) (distinct (k-Cons x1 x2) k-Nil)))
(assert (forall ((x1 T) (x2 T)) (distinct (k-Cons x1 x2) k-Zero)))
(assert (forall ((x1 T) (x2 T) (y1 T)) (distinct (k-Cons x1 x2) (k-Succ y1))))
(assert (distinct k-Nil k-True))
(assert (distinct k-Nil k-False))
(assert (forall ((y1 T) (y2 T)) (distinct k-Nil (k-Cons y1 y2))))
(assert (distinct k-Nil k-Zero))
(assert (forall ((y1 T)) (distinct k-Nil (k-Succ y1))))
(assert (distinct k-Zero k-True))
(assert (distinct k-Zero k-False))
(assert (forall ((y1 T) (y2 T)) (distinct k-Zero (k-Cons y1 y2))))
(assert (distinct k-Zero k-Nil))
(assert (forall ((y1 T)) (distinct k-Zero (k-Succ y1))))
(assert (forall ((x1 T)) (distinct (k-Succ x1) k-True)))
(assert (forall ((x1 T)) (distinct (k-Succ x1) k-False)))
(assert (forall ((x1 T) (y1 T) (y2 T)) (distinct (k-Succ x1) (k-Cons y1 y2))))
(assert (forall ((x1 T)) (distinct (k-Succ x1) k-Nil)))
(assert (forall ((x1 T)) (distinct (k-Succ x1) k-Zero)))
(assert (distinct k-True bad))
(assert (distinct k-True unr))
(assert (distinct k-False bad))
(assert (distinct k-False unr))
(assert (forall ((x1 T) (x2 T)) (distinct (k-Cons x1 x2) bad)))
(assert (forall ((x1 T) (x2 T)) (distinct (k-Cons x1 x2) unr)))
(assert (distinct k-Nil bad))
(assert (distinct k-Nil unr))
(assert (distinct k-Zero bad))
(assert (distinct k-Zero unr))
(assert (forall ((x1 T)) (distinct (k-Succ x1) bad)))
(assert (forall ((x1 T)) (distinct (k-Succ x1) unr)))
(assert (forall ((x1 T) (x2 T)) (= (sel-0-Cons (k-Cons x1 x2)) x1)))
(assert (forall ((x1 T) (x2 T)) (= (sel-1-Cons (k-Cons x1 x2)) x2)))
(assert (forall ((x1 T)) (= (sel-0-Succ (k-Succ x1)) x1)))
(assert (cf k-True))
(assert (cf k-False))
(assert (forall ((x1 T) (x2 T)) (= (cf (k-Cons x1 x2)) (and (cf x1) (cf x2)))))
(assert (cf k-Nil))
(assert (cf k-Zero))
(assert (forall ((x1 T)) (= (cf (k-Succ x1)) (cf x1))))
(assert (cf unr))
(assert (not (cf bad)))
(assert (forall ((xs T)) (= (f-cons? bad) bad)))
(assert (forall ((xs T)) (= (f-cons? k-Nil) k-False)))
(assert (forall ((xs T)) (= (f-cons? k-True) k-True)))
(assert (forall ((xs T)) (=> (and (distinct xs bad) (distinct xs k-Nil) (distinct xs k-True)) (= (f-cons? xs) unr))))
(assert (forall ((xs T)) (= (f-cons? xs) (app ptr-cons? xs))))
(assert (forall ((f T) (a T) (xs T)) (= (f-foldr f a bad) bad)))
(assert (forall ((f T) (a T) (xs T)) (= (f-foldr f a k-Nil) a)))
(assert (forall ((f T) (a T) (xs T) (z T) (zs T)) (= (f-foldr f a (k-Cons z zs)) (app (app f z) (app (app (app ptr-foldr f) a) zs)))))
(assert (forall ((f T) (a T) (xs T)) (=> (and (distinct xs bad) (distinct xs k-Nil) (distinct xs (k-Cons (sel-0-Cons xs) (sel-1-Cons xs)))) (= (f-foldr f a xs) unr))))
(assert (forall ((f T) (a T) (xs T)) (= (f-foldr f a xs) (app (app (app ptr-foldr f) a) xs))))
(assert (forall ((f T) (a T) (xs T)) (= (f-foldl f a bad) bad)))
(assert (forall ((f T) (a T) (xs T)) (= (f-foldl f a k-Nil) a)))
(assert (forall ((f T) (a T) (xs T) (z T) (zs T)) (= (f-foldl f a (k-Cons z zs)) (app (app (app ptr-rec-foldl f) (app (app f a) z)) zs))))
(assert (forall ((f T) (a T) (xs T)) (=> (and (distinct xs bad) (distinct xs k-Nil) (distinct xs (k-Cons (sel-0-Cons xs) (sel-1-Cons xs)))) (= (f-foldl f a xs) unr))))
(assert (forall ((f T) (a T) (xs T)) (= (f-foldl f a xs) (app (app (app ptr-foldl f) a) xs))))
(assert (forall ((f T) (xs T)) (= (f-map f xs) (app (app (app ptr-foldr (app ptr-map-foldr-step f)) k-Nil) xs))))
(assert (forall ((f T) (xs T)) (= (f-map f xs) (app (app ptr-map f) xs))))
(assert (forall ((f T) (x T) (ys T)) (= (f-map-foldr-step f x ys) (k-Cons (app f x) ys))))
(assert (forall ((f T) (x T) (ys T)) (= (f-map-foldr-step f x ys) (app (app (app ptr-map-foldr-step f) x) ys))))
(assert (forall ((xs T)) (= (f-reverse xs) (app (app (app ptr-foldl ptr-cons-eta) k-Nil) xs))))
(assert (forall ((xs T)) (= (f-reverse xs) (app ptr-reverse xs))))
(assert (forall ((x T) (xs T)) (= (f-cons-eta x xs) (k-Cons x xs))))
(assert (forall ((x T) (xs T)) (= (f-cons-eta x xs) (app (app ptr-cons-eta x) xs))))
(assert (forall ((xs T)) (= (f-head bad) bad)))
(assert (forall ((xs T)) (= (f-head k-Nil) bad)))
(assert (forall ((xs T) (z T) (zs T)) (= (f-head (k-Cons z zs)) z)))
(assert (forall ((xs T)) (=> (and (distinct xs bad) (distinct xs k-Nil) (distinct xs (k-Cons (sel-0-Cons xs) (sel-1-Cons xs)))) (= (f-head xs) unr))))
(assert (forall ((xs T)) (= (f-head xs) (app ptr-head xs))))
(assert (forall ((xs T)) (= (f-tail bad) bad)))
(assert (forall ((xs T)) (= (f-tail k-Nil) bad)))
(assert (forall ((xs T) (z T) (zs T)) (= (f-tail (k-Cons z zs)) zs)))
(assert (forall ((xs T)) (=> (and (distinct xs bad) (distinct xs k-Nil) (distinct xs (k-Cons (sel-0-Cons xs) (sel-1-Cons xs)))) (= (f-tail xs) unr))))
(assert (forall ((xs T)) (= (f-tail xs) (app ptr-tail xs))))
(assert (forall ((f T) (xs T)) (= (f-foldr1 f xs) (app (app (app ptr-foldr f) (app ptr-head xs)) (app ptr-tail xs)))))
(assert (forall ((f T) (xs T)) (= (f-foldr1 f xs) (app (app ptr-foldr1 f) xs))))
(assert
 (forall
  ((f T))
  (=> (forall ((x T)) (=> (cf x) (forall ((y T)) (=> (cf y) (cf (app (app f x) y)))))) (forall ((a T)) (=> (cf a) (forall ((xs T)) (=> (cf xs) (cf (app (app (app ptr-rec-foldl f) a) xs)))))))))
(assert
 (not
  (forall ((f T)) (=> (forall ((x T)) (=> (cf x) (forall ((y T)) (=> (cf y) (cf (app (app f x) y)))))) (forall ((a T)) (=> (cf a) (forall ((xs T)) (=> (cf xs) (cf (app (app (app ptr-foldl f) a) xs))))))))))
(check-sat)