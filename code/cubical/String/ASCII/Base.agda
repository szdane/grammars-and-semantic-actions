-- Subset of ASCII characters for writing test cases
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module String.ASCII.Base where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.SumFin
open import Cubical.Data.FinSet
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
import Cubical.Data.Empty as Empty
open import Cubical.Data.List as List
open import Cubical.Data.List.FinData


private
  variable
    ℓ' ℓ'' : Level

data ASCIIChar : Type ℓ-zero where
  SPACE NEWLINE TAB EXLCAM POUND
    SINGLEQUOTE DOUBLEQUOTE DOLLAR PERCENT
    AMPERSAND LPAREN RPAREN ASTERISK PLUS COMMA
    MINUS PERIOD FSLASH BSLASH COLON SEMICOLON
    GT EQ LT QUESTION AT LBRACKET RBRACKET CARROT
    UNDERSCORE BACKTICK TILDE LCURLY RCURLY VERTBAR
    A^ B^ C^ D^ E^ F^ G^ H^ I^ J^ K^ L^ M^
    N^ O^ P^ Q^ R^ S^ T^ U^ V^ W^ X^ Y^ Z^
    a^ b^ c^ d^ e^ f^ g^ h^ i^ j^ k^ l^ m^
    n^ o^ p^ q^ r^ s^ t^ u^ v^ w^ x^ y^ z^
    zero^ one^ two^ three^ four^ five^
    six^ seven^ eight^ nine^
    : ASCIIChar

open import String.Unicode
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.List

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties

translation : List (UnicodeChar × ASCIIChar)
translation =
  (' ' , SPACE) ∷ ('\n' , NEWLINE) ∷ ('\t' , TAB) ∷
  ('!' , EXLCAM) ∷ ('#' , POUND) ∷
  ('\'' , SINGLEQUOTE) ∷ ('"' , DOUBLEQUOTE) ∷
  ('$' , DOLLAR) ∷ ('%' , PERCENT) ∷
  ('&' , AMPERSAND) ∷ ('(' , LPAREN) ∷
  (')' , RPAREN) ∷ ('*' , ASTERISK) ∷
  ('+' , PLUS) ∷ (',' , COMMA) ∷ ('-' , MINUS) ∷
  ('.' , PERIOD) ∷ ('/' , FSLASH) ∷
  ('\\' , BSLASH) ∷ (':' , COLON) ∷
  (';' , SEMICOLON) ∷ ('>' , GT) ∷ ('=' , EQ) ∷
  ('<' , LT) ∷ ('?' , QUESTION) ∷ ('@' , AT) ∷
  ('[' , LBRACKET) ∷ (']' , RBRACKET) ∷
  ('^' , CARROT) ∷ ('_' , UNDERSCORE) ∷
  ('`' , BACKTICK) ∷ ('~' , TILDE) ∷
  ('{' , LCURLY) ∷ ('}' , RCURLY) ∷
  ('|' , VERTBAR) ∷ ('A' , A^) ∷ ('B' , B^) ∷
  ('C' , C^) ∷ ('D' , D^) ∷ ('E' , E^) ∷
  ('F' , F^) ∷ ('G' , G^) ∷ ('H' , H^) ∷
  ('I' , I^) ∷ ('J' , J^) ∷ ('K' , K^) ∷
  ('L' , L^) ∷ ('M' , M^) ∷ ('N' , N^) ∷
  ('O' , O^) ∷ ('P' , P^) ∷ ('Q' , Q^) ∷
  ('R' , R^) ∷ ('S' , S^) ∷ ('T' , T^) ∷
  ('U' , U^) ∷ ('V' , V^) ∷ ('W' , W^) ∷
  ('X' , X^) ∷ ('Y' , Y^) ∷ ('Z' , Z^) ∷
  ('a' , a^) ∷ ('b' , b^) ∷ ('c' , c^) ∷
  ('d' , d^) ∷ ('e' , e^) ∷ ('f' , f^) ∷
  ('g' , g^) ∷ ('h' , h^) ∷ ('i' , i^) ∷
  ('j' , j^) ∷ ('k' , k^) ∷ ('l' , l^) ∷
  ('m' , m^) ∷ ('n' , n^) ∷ ('o' , o^) ∷
  ('p' , p^) ∷ ('q' , q^) ∷ ('r' , r^) ∷
  ('s' , s^) ∷ ('t' , t^) ∷ ('u' , u^) ∷
  ('v' , v^) ∷ ('w' , w^) ∷ ('x' , x^) ∷
  ('y' , y^) ∷ ('z' , z^) ∷ ('0' , zero^) ∷
  ('1' , one^) ∷ ('2' , two^) ∷ ('3' , three^) ∷
  ('4' , four^) ∷ ('5' , five^) ∷ ('6' , six^) ∷
  ('7' , seven^) ∷ ('8' , eight^) ∷ ('9' , nine^) ∷
  []

-- TODO move this
module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'}
  (discA : Discrete A) where
  find : List (A × B) → (a : A) → Maybe B
  find [] the-a = nothing
  find ((a' , b') ∷ abs) the-a =
    decRec
      (λ _ → just b')
      (λ _ → find abs the-a)
      (discA a' the-a)

  findIdx : List (A × B) → (a : A) → ℕ → Maybe ℕ
  findIdx [] the-a n = nothing
  findIdx ((a' , b') ∷ abs) the-a n =
    decRec
      (λ _ → just n)
      (λ _ → findIdx abs the-a (suc n))
      (discA a' the-a)

Unicode→ASCII : UnicodeChar → Maybe ASCIIChar
Unicode→ASCII = find DiscreteUnicodeChar translation

_ : 97 ≡ length translation
_ = refl

ASCII→Fin : ASCIIChar → Fin 97
ASCII→Fin SPACE =       fromℕ {k = 96} 0
ASCII→Fin NEWLINE =     fromℕ {k = 96} 1
ASCII→Fin TAB =         fromℕ {k = 96} 2
ASCII→Fin EXLCAM =      fromℕ {k = 96} 3
ASCII→Fin POUND =       fromℕ {k = 96} 4
ASCII→Fin SINGLEQUOTE = fromℕ {k = 96} 5
ASCII→Fin DOUBLEQUOTE = fromℕ {k = 96} 6
ASCII→Fin DOLLAR =      fromℕ {k = 96} 7
ASCII→Fin PERCENT =     fromℕ {k = 96} 8
ASCII→Fin AMPERSAND =   fromℕ {k = 96} 9
ASCII→Fin LPAREN =      fromℕ {k = 96} 10
ASCII→Fin RPAREN =      fromℕ {k = 96} 11
ASCII→Fin ASTERISK =    fromℕ {k = 96} 12
ASCII→Fin PLUS =        fromℕ {k = 96} 13
ASCII→Fin COMMA =       fromℕ {k = 96} 14
ASCII→Fin MINUS =       fromℕ {k = 96} 15
ASCII→Fin PERIOD =      fromℕ {k = 96} 16
ASCII→Fin FSLASH =      fromℕ {k = 96} 17
ASCII→Fin BSLASH =      fromℕ {k = 96} 18
ASCII→Fin COLON =       fromℕ {k = 96} 19
ASCII→Fin SEMICOLON =   fromℕ {k = 96} 20
ASCII→Fin GT =          fromℕ {k = 96} 21
ASCII→Fin EQ =          fromℕ {k = 96} 22
ASCII→Fin LT =          fromℕ {k = 96} 23
ASCII→Fin QUESTION =    fromℕ {k = 96} 24
ASCII→Fin AT =          fromℕ {k = 96} 25
ASCII→Fin LBRACKET =    fromℕ {k = 96} 26
ASCII→Fin RBRACKET =    fromℕ {k = 96} 27
ASCII→Fin CARROT =      fromℕ {k = 96} 28
ASCII→Fin UNDERSCORE =  fromℕ {k = 96} 29
ASCII→Fin BACKTICK =    fromℕ {k = 96} 30
ASCII→Fin TILDE =       fromℕ {k = 96} 31
ASCII→Fin LCURLY =      fromℕ {k = 96} 32
ASCII→Fin RCURLY =      fromℕ {k = 96} 33
ASCII→Fin VERTBAR =     fromℕ {k = 96} 34
ASCII→Fin A^ =          fromℕ {k = 96} 35
ASCII→Fin B^ =          fromℕ {k = 96} 36
ASCII→Fin C^ =          fromℕ {k = 96} 37
ASCII→Fin D^ =          fromℕ {k = 96} 38
ASCII→Fin E^ =          fromℕ {k = 96} 39
ASCII→Fin F^ =          fromℕ {k = 96} 40
ASCII→Fin G^ =          fromℕ {k = 96} 41
ASCII→Fin H^ =          fromℕ {k = 96} 42
ASCII→Fin I^ =          fromℕ {k = 96} 43
ASCII→Fin J^ =          fromℕ {k = 96} 44
ASCII→Fin K^ =          fromℕ {k = 96} 45
ASCII→Fin L^ =          fromℕ {k = 96} 46
ASCII→Fin M^ =          fromℕ {k = 96} 47
ASCII→Fin N^ =          fromℕ {k = 96} 48
ASCII→Fin O^ =          fromℕ {k = 96} 49
ASCII→Fin P^ =          fromℕ {k = 96} 50
ASCII→Fin Q^ =          fromℕ {k = 96} 51
ASCII→Fin R^ =          fromℕ {k = 96} 52
ASCII→Fin S^ =          fromℕ {k = 96} 53
ASCII→Fin T^ =          fromℕ {k = 96} 54
ASCII→Fin U^ =          fromℕ {k = 96} 55
ASCII→Fin V^ =          fromℕ {k = 96} 56
ASCII→Fin W^ =          fromℕ {k = 96} 57
ASCII→Fin X^ =          fromℕ {k = 96} 58
ASCII→Fin Y^ =          fromℕ {k = 96} 59
ASCII→Fin Z^ =          fromℕ {k = 96} 60
ASCII→Fin a^ =          fromℕ {k = 96} 61
ASCII→Fin b^ =          fromℕ {k = 96} 62
ASCII→Fin c^ =          fromℕ {k = 96} 63
ASCII→Fin d^ =          fromℕ {k = 96} 64
ASCII→Fin e^ =          fromℕ {k = 96} 65
ASCII→Fin f^ =          fromℕ {k = 96} 66
ASCII→Fin g^ =          fromℕ {k = 96} 67
ASCII→Fin h^ =          fromℕ {k = 96} 68
ASCII→Fin i^ =          fromℕ {k = 96} 69
ASCII→Fin j^ =          fromℕ {k = 96} 70
ASCII→Fin k^ =          fromℕ {k = 96} 71
ASCII→Fin l^ =          fromℕ {k = 96} 72
ASCII→Fin m^ =          fromℕ {k = 96} 73
ASCII→Fin n^ =          fromℕ {k = 96} 74
ASCII→Fin o^ =          fromℕ {k = 96} 75
ASCII→Fin p^ =          fromℕ {k = 96} 76
ASCII→Fin q^ =          fromℕ {k = 96} 77
ASCII→Fin r^ =          fromℕ {k = 96} 78
ASCII→Fin s^ =          fromℕ {k = 96} 79
ASCII→Fin t^ =          fromℕ {k = 96} 80
ASCII→Fin u^ =          fromℕ {k = 96} 81
ASCII→Fin v^ =          fromℕ {k = 96} 82
ASCII→Fin w^ =          fromℕ {k = 96} 83
ASCII→Fin x^ =          fromℕ {k = 96} 84
ASCII→Fin y^ =          fromℕ {k = 96} 85
ASCII→Fin z^ =          fromℕ {k = 96} 86
ASCII→Fin zero^ =       fromℕ {k = 96} 87
ASCII→Fin one^ =        fromℕ {k = 96} 88
ASCII→Fin two^ =        fromℕ {k = 96} 89
ASCII→Fin three^ =      fromℕ {k = 96} 90
ASCII→Fin four^ =       fromℕ {k = 96} 91
ASCII→Fin five^ =       fromℕ {k = 96} 92
ASCII→Fin six^ =        fromℕ {k = 96} 93
ASCII→Fin seven^ =      fromℕ {k = 96} 94
ASCII→Fin eight^ =      fromℕ {k = 96} 95
ASCII→Fin nine^ =       fromℕ {k = 96} 96

-- This is incredibly ugly but works
-- Agda has issues pattern matching on nat literals
-- larger than 20, so I need to manually expand out
-- each num with its explicit constructors
-- It would be really nice to have some sort of macro
-- to define an enumerated type and automatically prove
-- that it is a FinSet
Fin→ASCII : Fin 97 → ASCIIChar
Fin→ASCII (fzero) = SPACE
Fin→ASCII (fsuc fzero) = NEWLINE
Fin→ASCII (fsuc (fsuc fzero)) = TAB
Fin→ASCII (fsuc (fsuc (fsuc fzero))) = EXLCAM
Fin→ASCII (fsuc ( fsuc (fsuc (fsuc fzero))  )) = POUND
Fin→ASCII (fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) )) = SINGLEQUOTE
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) )) = DOUBLEQUOTE
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) )) = DOLLAR
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) )) = PERCENT
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) )) = AMPERSAND
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) )) = LPAREN
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) )) = RPAREN
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) )) = ASTERISK
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) )) = PLUS
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) )) = COMMA
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) )) = MINUS
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) )) = PERIOD
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) )) = FSLASH
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = BSLASH
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = COLON
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = SEMICOLON
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = GT
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = EQ
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = LT
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = QUESTION
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = AT
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = LBRACKET
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = RBRACKET
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = CARROT
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = UNDERSCORE
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = BACKTICK
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = TILDE
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = LCURLY
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = RCURLY
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = VERTBAR
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = A^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = B^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = C^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = D^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = E^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = F^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = G^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = H^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = I^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = J^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = K^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = L^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = M^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = N^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = O^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = P^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = Q^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = R^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = S^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = T^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = U^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = V^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = W^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = X^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = Y^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = Z^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = a^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = b^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = c^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = d^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = e^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = f^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = g^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = h^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = i^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = j^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = k^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = l^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = m^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = n^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = o^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = p^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = q^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = r^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = s^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = t^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = u^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = v^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = w^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = x^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = y^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = z^
Fin→ASCII (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) = zero^
Fin→ASCII (fsuc (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) = one^
Fin→ASCII (fsuc (fsuc (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) = two^
Fin→ASCII (fsuc (fsuc (fsuc (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) = three^
Fin→ASCII (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) = four^
Fin→ASCII (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) = five^
Fin→ASCII (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) = six^
Fin→ASCII (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) = seven^
Fin→ASCII (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) = eight^
Fin→ASCII (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) = nine^

ASCIIFinRetract : (c : ASCIIChar) → Fin→ASCII (ASCII→Fin c) ≡ c
ASCIIFinRetract SPACE = refl
ASCIIFinRetract NEWLINE = refl
ASCIIFinRetract TAB = refl
ASCIIFinRetract EXLCAM = refl
ASCIIFinRetract POUND = refl
ASCIIFinRetract SINGLEQUOTE = refl
ASCIIFinRetract DOUBLEQUOTE = refl
ASCIIFinRetract DOLLAR = refl
ASCIIFinRetract PERCENT = refl
ASCIIFinRetract AMPERSAND = refl
ASCIIFinRetract LPAREN = refl
ASCIIFinRetract RPAREN = refl
ASCIIFinRetract ASTERISK = refl
ASCIIFinRetract PLUS = refl
ASCIIFinRetract COMMA = refl
ASCIIFinRetract MINUS = refl
ASCIIFinRetract PERIOD = refl
ASCIIFinRetract FSLASH = refl
ASCIIFinRetract BSLASH = refl
ASCIIFinRetract COLON = refl
ASCIIFinRetract SEMICOLON = refl
ASCIIFinRetract GT = refl
ASCIIFinRetract EQ = refl
ASCIIFinRetract LT = refl
ASCIIFinRetract QUESTION = refl
ASCIIFinRetract AT = refl
ASCIIFinRetract LBRACKET = refl
ASCIIFinRetract RBRACKET = refl
ASCIIFinRetract CARROT = refl
ASCIIFinRetract UNDERSCORE = refl
ASCIIFinRetract BACKTICK = refl
ASCIIFinRetract TILDE = refl
ASCIIFinRetract LCURLY = refl
ASCIIFinRetract RCURLY = refl
ASCIIFinRetract VERTBAR = refl
ASCIIFinRetract A^ = refl
ASCIIFinRetract B^ = refl
ASCIIFinRetract C^ = refl
ASCIIFinRetract D^ = refl
ASCIIFinRetract E^ = refl
ASCIIFinRetract F^ = refl
ASCIIFinRetract G^ = refl
ASCIIFinRetract H^ = refl
ASCIIFinRetract I^ = refl
ASCIIFinRetract J^ = refl
ASCIIFinRetract K^ = refl
ASCIIFinRetract L^ = refl
ASCIIFinRetract M^ = refl
ASCIIFinRetract N^ = refl
ASCIIFinRetract O^ = refl
ASCIIFinRetract P^ = refl
ASCIIFinRetract Q^ = refl
ASCIIFinRetract R^ = refl
ASCIIFinRetract S^ = refl
ASCIIFinRetract T^ = refl
ASCIIFinRetract U^ = refl
ASCIIFinRetract V^ = refl
ASCIIFinRetract W^ = refl
ASCIIFinRetract X^ = refl
ASCIIFinRetract Y^ = refl
ASCIIFinRetract Z^ = refl
ASCIIFinRetract a^ = refl
ASCIIFinRetract b^ = refl
ASCIIFinRetract c^ = refl
ASCIIFinRetract d^ = refl
ASCIIFinRetract e^ = refl
ASCIIFinRetract f^ = refl
ASCIIFinRetract g^ = refl
ASCIIFinRetract h^ = refl
ASCIIFinRetract i^ = refl
ASCIIFinRetract j^ = refl
ASCIIFinRetract k^ = refl
ASCIIFinRetract l^ = refl
ASCIIFinRetract m^ = refl
ASCIIFinRetract n^ = refl
ASCIIFinRetract o^ = refl
ASCIIFinRetract p^ = refl
ASCIIFinRetract q^ = refl
ASCIIFinRetract r^ = refl
ASCIIFinRetract s^ = refl
ASCIIFinRetract t^ = refl
ASCIIFinRetract u^ = refl
ASCIIFinRetract v^ = refl
ASCIIFinRetract w^ = refl
ASCIIFinRetract x^ = refl
ASCIIFinRetract y^ = refl
ASCIIFinRetract z^ = refl
ASCIIFinRetract zero^ = refl
ASCIIFinRetract one^ = refl
ASCIIFinRetract two^ = refl
ASCIIFinRetract three^ = refl
ASCIIFinRetract four^ = refl
ASCIIFinRetract five^ = refl
ASCIIFinRetract six^ = refl
ASCIIFinRetract seven^ = refl
ASCIIFinRetract eight^ = refl
ASCIIFinRetract nine^ = refl

ASCIIFinSection : (n : Fin 97) → (ASCII→Fin (Fin→ASCII n)) ≡ n
ASCIIFinSection (fzero) = refl
ASCIIFinSection (fsuc fzero) = refl
ASCIIFinSection (fsuc (fsuc fzero)) = refl
ASCIIFinSection (fsuc (fsuc (fsuc fzero))) = refl
ASCIIFinSection (fsuc ( fsuc (fsuc (fsuc fzero))  )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))  = refl
ASCIIFinSection (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) ) = refl
ASCIIFinSection (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) ) = refl
ASCIIFinSection (fsuc (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) ) ) = refl
ASCIIFinSection (fsuc (fsuc (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) ) ) ) = refl
ASCIIFinSection (fsuc (fsuc (fsuc (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) ) ) ) ) = refl
ASCIIFinSection (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) ) ) ) ) ) = refl
ASCIIFinSection (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) ) ) ) ) ) ) = refl
ASCIIFinSection (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) ) ) ) ) ) ) ) = refl
ASCIIFinSection (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) ) ) ) ) ) ) ) ) = refl
ASCIIFinSection (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) ) ) ) ) ) ) ) ) ) = refl
ASCIIFinSection (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) ) ) ) ) ) ) ) ) ) ) = refl
opaque
  isSetASCIIChar : isSet ASCIIChar
  isSetASCIIChar =
    isSetRetract ASCII→Fin Fin→ASCII
      ASCIIFinRetract (isSetFin {97})

ASCII : hSet ℓ-zero
ASCII = ASCIIChar , isSetASCIIChar
-- isSetASCIIChar
ASCII≅Fin : Iso ASCIIChar (Fin 97)
ASCII≅Fin = iso ASCII→Fin Fin→ASCII ASCIIFinSection ASCIIFinRetract

ASCII≃Fin : ASCIIChar ≃ Fin 97
ASCII≃Fin = isoToEquiv ASCII≅Fin

isFinSetASCIIChar : isFinSet ASCIIChar
isFinSetASCIIChar = EquivPresIsFinSet (invEquiv ASCII≃Fin) (isFinSetFin {97})

DiscreteASCIIChar : Discrete ASCIIChar
DiscreteASCIIChar = isFinSet→Discrete isFinSetASCIIChar
