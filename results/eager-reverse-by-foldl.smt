; given: foldl  ∈  (CF CF -> CF) CF CF -> CF
; prove: reverse  ∈  CF -> CF
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
(assert (forall ((x T)) (=> (distinct x unr) (= (app x bad) bad))))
(assert (forall ((x T)) (=> (distinct x bad) (= (app x unr) unr))))
(assert (distinct bad unr))
(assert (distinct k-True k-False))
(assert (forall ((y1 T) (y2 T)) (=> (and (and (distinct k-True bad) (distinct k-True unr)) (and (distinct (k-Cons y1 y2) bad) (distinct (k-Cons y1 y2) unr))) (distinct k-True (k-Cons y1 y2)))))
(assert (distinct k-True k-Nil))
(assert (distinct k-True k-Zero))
(assert (forall ((y1 T)) (=> (and (and (distinct k-True bad) (distinct k-True unr)) (and (distinct (k-Succ y1) bad) (distinct (k-Succ y1) unr))) (distinct k-True (k-Succ y1)))))
(assert (distinct k-False k-True))
(assert (forall ((y1 T) (y2 T)) (=> (and (and (distinct k-False bad) (distinct k-False unr)) (and (distinct (k-Cons y1 y2) bad) (distinct (k-Cons y1 y2) unr))) (distinct k-False (k-Cons y1 y2)))))
(assert (distinct k-False k-Nil))
(assert (distinct k-False k-Zero))
(assert (forall ((y1 T)) (=> (and (and (distinct k-False bad) (distinct k-False unr)) (and (distinct (k-Succ y1) bad) (distinct (k-Succ y1) unr))) (distinct k-False (k-Succ y1)))))
(assert (forall ((x1 T) (x2 T)) (=> (and (and (distinct (k-Cons x1 x2) bad) (distinct (k-Cons x1 x2) unr)) (and (distinct k-True bad) (distinct k-True unr))) (distinct (k-Cons x1 x2) k-True))))
(assert (forall ((x1 T) (x2 T)) (=> (and (and (distinct (k-Cons x1 x2) bad) (distinct (k-Cons x1 x2) unr)) (and (distinct k-False bad) (distinct k-False unr))) (distinct (k-Cons x1 x2) k-False))))
(assert (forall ((x1 T) (x2 T)) (=> (and (and (distinct (k-Cons x1 x2) bad) (distinct (k-Cons x1 x2) unr)) (and (distinct k-Nil bad) (distinct k-Nil unr))) (distinct (k-Cons x1 x2) k-Nil))))
(assert (forall ((x1 T) (x2 T)) (=> (and (and (distinct (k-Cons x1 x2) bad) (distinct (k-Cons x1 x2) unr)) (and (distinct k-Zero bad) (distinct k-Zero unr))) (distinct (k-Cons x1 x2) k-Zero))))
(assert
 (forall
  ((x1 T) (x2 T) (y1 T))
  (=> (and (and (distinct (k-Cons x1 x2) bad) (distinct (k-Cons x1 x2) unr)) (and (distinct (k-Succ y1) bad) (distinct (k-Succ y1) unr))) (distinct (k-Cons x1 x2) (k-Succ y1)))))
(assert (distinct k-Nil k-True))
(assert (distinct k-Nil k-False))
(assert (forall ((y1 T) (y2 T)) (=> (and (and (distinct k-Nil bad) (distinct k-Nil unr)) (and (distinct (k-Cons y1 y2) bad) (distinct (k-Cons y1 y2) unr))) (distinct k-Nil (k-Cons y1 y2)))))
(assert (distinct k-Nil k-Zero))
(assert (forall ((y1 T)) (=> (and (and (distinct k-Nil bad) (distinct k-Nil unr)) (and (distinct (k-Succ y1) bad) (distinct (k-Succ y1) unr))) (distinct k-Nil (k-Succ y1)))))
(assert (distinct k-Zero k-True))
(assert (distinct k-Zero k-False))
(assert (forall ((y1 T) (y2 T)) (=> (and (and (distinct k-Zero bad) (distinct k-Zero unr)) (and (distinct (k-Cons y1 y2) bad) (distinct (k-Cons y1 y2) unr))) (distinct k-Zero (k-Cons y1 y2)))))
(assert (distinct k-Zero k-Nil))
(assert (forall ((y1 T)) (=> (and (and (distinct k-Zero bad) (distinct k-Zero unr)) (and (distinct (k-Succ y1) bad) (distinct (k-Succ y1) unr))) (distinct k-Zero (k-Succ y1)))))
(assert (forall ((x1 T)) (=> (and (and (distinct (k-Succ x1) bad) (distinct (k-Succ x1) unr)) (and (distinct k-True bad) (distinct k-True unr))) (distinct (k-Succ x1) k-True))))
(assert (forall ((x1 T)) (=> (and (and (distinct (k-Succ x1) bad) (distinct (k-Succ x1) unr)) (and (distinct k-False bad) (distinct k-False unr))) (distinct (k-Succ x1) k-False))))
(assert
 (forall
  ((x1 T) (y1 T) (y2 T))
  (=> (and (and (distinct (k-Succ x1) bad) (distinct (k-Succ x1) unr)) (and (distinct (k-Cons y1 y2) bad) (distinct (k-Cons y1 y2) unr))) (distinct (k-Succ x1) (k-Cons y1 y2)))))
(assert (forall ((x1 T)) (=> (and (and (distinct (k-Succ x1) bad) (distinct (k-Succ x1) unr)) (and (distinct k-Nil bad) (distinct k-Nil unr))) (distinct (k-Succ x1) k-Nil))))
(assert (forall ((x1 T)) (=> (and (and (distinct (k-Succ x1) bad) (distinct (k-Succ x1) unr)) (and (distinct k-Zero bad) (distinct k-Zero unr))) (distinct (k-Succ x1) k-Zero))))
(assert (distinct k-True bad))
(assert (distinct k-True unr))
(assert (distinct k-False bad))
(assert (distinct k-False unr))
(assert (forall ((x0 T) (x1 T)) (= (or (= x0 bad) (and (= x1 bad) (distinct x0 unr))) (= (k-Cons x0 x1) bad))))
(assert (forall ((x0 T) (x1 T)) (= (or (= x0 unr) (and (= x1 unr) (distinct x0 bad))) (= (k-Cons x0 x1) unr))))
(assert (distinct k-Nil bad))
(assert (distinct k-Nil unr))
(assert (distinct k-Zero bad))
(assert (distinct k-Zero unr))
(assert (forall ((x0 T)) (= (= x0 bad) (= (k-Succ x0) bad))))
(assert (forall ((x0 T)) (= (= x0 unr) (= (k-Succ x0) unr))))
(assert (forall ((x1 T) (x2 T)) (=> (and (and (distinct x1 bad) (distinct x1 unr)) (and (distinct x2 bad) (distinct x2 unr))) (= (sel-0-Cons (k-Cons x1 x2)) x1))))
(assert (forall ((x1 T) (x2 T)) (= (= (k-Cons x1 x2) bad) (= (sel-0-Cons (k-Cons x1 x2)) bad))))
(assert (forall ((x1 T) (x2 T)) (= (= (k-Cons x1 x2) unr) (= (sel-0-Cons (k-Cons x1 x2)) unr))))
(assert (forall ((x1 T) (x2 T)) (=> (and (and (distinct x1 bad) (distinct x1 unr)) (and (distinct x2 bad) (distinct x2 unr))) (= (sel-1-Cons (k-Cons x1 x2)) x2))))
(assert (forall ((x1 T) (x2 T)) (= (= (k-Cons x1 x2) bad) (= (sel-1-Cons (k-Cons x1 x2)) bad))))
(assert (forall ((x1 T) (x2 T)) (= (= (k-Cons x1 x2) unr) (= (sel-1-Cons (k-Cons x1 x2)) unr))))
(assert (forall ((x1 T)) (=> (and (distinct x1 bad) (distinct x1 unr)) (= (sel-0-Succ (k-Succ x1)) x1))))
(assert (forall ((x1 T)) (= (= (k-Succ x1) bad) (= (sel-0-Succ (k-Succ x1)) bad))))
(assert (forall ((x1 T)) (= (= (k-Succ x1) unr) (= (sel-0-Succ (k-Succ x1)) unr))))
(assert (cf k-True))
(assert (cf k-False))
(assert (forall ((x1 T) (x2 T)) (= (cf (k-Cons x1 x2)) (and (cf x1) (cf x2)))))
(assert (cf k-Nil))
(assert (cf k-Zero))
(assert (forall ((x1 T)) (= (cf (k-Succ x1)) (cf x1))))
(assert (cf unr))
(assert (not (cf bad)))
(assert
 (forall
  ((xs T))
  (=>
   (and (distinct xs bad) (distinct xs unr))
   (and (= (f-cons? bad) bad) (= (f-cons? k-Nil) k-False) (= (f-cons? k-True) k-True) (=> (and (distinct xs bad) (distinct xs k-Nil) (distinct xs k-True)) (= (f-cons? xs) unr))))))
(assert (forall ((xs T)) (= (f-cons? xs) (app ptr-cons? xs))))
(assert
 (forall
  ((f T) (a T) (xs T))
  (=>
   (and (and (distinct f bad) (distinct f unr)) (and (distinct a bad) (distinct a unr)) (and (distinct xs bad) (distinct xs unr)))
   (and (= (f-foldr f a bad) bad)
        (= (f-foldr f a k-Nil) a)
        (forall ((z T) (zs T)) (= (f-foldr f a (k-Cons z zs)) (app (app f z) (app (app (app ptr-foldr f) a) zs))))
        (=> (and (distinct xs bad) (distinct xs k-Nil) (distinct xs (k-Cons (sel-0-Cons xs) (sel-1-Cons xs)))) (= (f-foldr f a xs) unr))))))
(assert (forall ((f T) (a T) (xs T)) (= (f-foldr f a xs) (app (app (app ptr-foldr f) a) xs))))
(assert
 (forall
  ((f T) (a T) (xs T))
  (=>
   (and (and (distinct f bad) (distinct f unr)) (and (distinct a bad) (distinct a unr)) (and (distinct xs bad) (distinct xs unr)))
   (and (= (f-foldl f a bad) bad)
        (= (f-foldl f a k-Nil) a)
        (forall ((z T) (zs T)) (= (f-foldl f a (k-Cons z zs)) (app (app (app ptr-foldl f) (app (app f a) z)) zs)))
        (=> (and (distinct xs bad) (distinct xs k-Nil) (distinct xs (k-Cons (sel-0-Cons xs) (sel-1-Cons xs)))) (= (f-foldl f a xs) unr))))))
(assert (forall ((f T) (a T) (xs T)) (= (f-foldl f a xs) (app (app (app ptr-foldl f) a) xs))))
(assert (forall ((f T) (xs T)) (=> (and (and (distinct f bad) (distinct f unr)) (and (distinct xs bad) (distinct xs unr))) (= (f-map f xs) (app (app (app ptr-foldr (app ptr-map-foldr-step f)) k-Nil) xs)))))
(assert (forall ((f T) (xs T)) (= (f-map f xs) (app (app ptr-map f) xs))))
(assert
 (forall
  ((f T) (x T) (ys T))
  (=> (and (and (distinct f bad) (distinct f unr)) (and (distinct x bad) (distinct x unr)) (and (distinct ys bad) (distinct ys unr))) (= (f-map-foldr-step f x ys) (k-Cons (app f x) ys)))))
(assert (forall ((f T) (x T) (ys T)) (= (f-map-foldr-step f x ys) (app (app (app ptr-map-foldr-step f) x) ys))))
(assert (forall ((xs T)) (=> (and (distinct xs bad) (distinct xs unr)) (= (f-reverse xs) (app (app (app ptr-foldl ptr-cons-eta) k-Nil) xs)))))
(assert (forall ((xs T)) (= (f-reverse xs) (app ptr-reverse xs))))
(assert (forall ((x T) (xs T)) (=> (and (and (distinct x bad) (distinct x unr)) (and (distinct xs bad) (distinct xs unr))) (= (f-cons-eta x xs) (k-Cons x xs)))))
(assert (forall ((x T) (xs T)) (= (f-cons-eta x xs) (app (app ptr-cons-eta x) xs))))
(assert
 (forall
  ((xs T))
  (=>
   (and (distinct xs bad) (distinct xs unr))
   (and (= (f-head bad) bad)
        (= (f-head k-Nil) bad)
        (forall ((z T) (zs T)) (= (f-head (k-Cons z zs)) z))
        (=> (and (distinct xs bad) (distinct xs k-Nil) (distinct xs (k-Cons (sel-0-Cons xs) (sel-1-Cons xs)))) (= (f-head xs) unr))))))
(assert (forall ((xs T)) (= (f-head xs) (app ptr-head xs))))
(assert
 (forall
  ((xs T))
  (=>
   (and (distinct xs bad) (distinct xs unr))
   (and (= (f-tail bad) bad)
        (= (f-tail k-Nil) bad)
        (forall ((z T) (zs T)) (= (f-tail (k-Cons z zs)) zs))
        (=> (and (distinct xs bad) (distinct xs k-Nil) (distinct xs (k-Cons (sel-0-Cons xs) (sel-1-Cons xs)))) (= (f-tail xs) unr))))))
(assert (forall ((xs T)) (= (f-tail xs) (app ptr-tail xs))))
(assert
 (forall ((f T) (xs T)) (=> (and (and (distinct f bad) (distinct f unr)) (and (distinct xs bad) (distinct xs unr))) (= (f-foldr1 f xs) (app (app (app ptr-foldr f) (app ptr-head xs)) (app ptr-tail xs))))))
(assert (forall ((f T) (xs T)) (= (f-foldr1 f xs) (app (app ptr-foldr1 f) xs))))
(assert
 (forall ((f T)) (=> (forall ((x T)) (=> (cf x) (forall ((y T)) (=> (cf y) (cf (app (app f x) y)))))) (forall ((a T)) (=> (cf a) (forall ((xs T)) (=> (cf xs) (cf (app (app (app ptr-foldl f) a) xs)))))))))
(assert (forall ((x T)) (=> (cf x) (cf (app ptr-rec-reverse x)))))
(assert (not (forall ((x T)) (=> (cf x) (cf (app ptr-reverse x))))))
(check-sat)