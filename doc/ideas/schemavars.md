# Schemavariablen im ProofScript

Fragestellung: Was wird in Variablen nach einem "match"-Aufruf gespeichert?

Beispielsweise:

Sequenz:
```
p(x + 2), x = 5
==>
p(7)
```
Proof Script:
```
match on='p(x + 2)' as=?var
```

Sollte jetzt in `?var` ein Term oder eine Position oder beides gespeichert werden?

## 1. Speichern eines Terms

Bei dieser Variante wird ein der gefundene Term selbst in der Variablen gespeichert.

Nachteil hier ist Uneindeutigkeit bei der Verwendung von gefundenen Variablen:

Diese Sequenz
```
p(a + 0), p(a * 2), a = f(a)
```

mit diesem Skript:
```
match on='p(?x * 2)'
applyEq on=?x with='a = f(a)'
```

führt wahrscheinlich nicht zu dem erwarteten Effekt. Ziel des Skriptautors war es sicherlich, `p(a * 2)` durch `p(f(a) * 2)` zu ersetzen, aber `applyEq` kann das zu diesem Zeitpunkt nicht wissen. Alles was die Regel an Information zur verfügung hat ist die Variablenzuweisung `?x = 'a'`.

## 2. Speichern von Position

Eine Möglichkeit wäre es, ein Tupel aus `ProofNodeSelector` und `TermSelector` zu speichern, welche an jeder stelle des Proofscripts der Variable eine eindeutige Position zuweist. Es wäre also auch immer möglich, den Term selbst zu bekommen. Z.B. über eine Funktion, etwa so:

`?term = get(?var)`

In dieser Variante gibt es die Unterscheidung zwischen Termen und Variablen, also ist `?var` etwas anderes als `?term`. Man kommt von Term zu Positionen indem man `match` bzw. `matchPos` aufruft, und von Positionen zu Termen über `get()`.

Positionen sollen hier vollkommen first-class werden, also kann ich etwa auch das Positions-Tupel auseinander bauen mit den Funktionen `termSelector(?var)` und (der vielleicht überflüssigen Funktion) `proofNodeSelector(?var)`, die die jeweiligen Selektoren extrahieren. Und Positionen können dann wieder gebaut werden, indem man einen Konstruktor `Pos(proofNodeSelector(?var), termSelector(?var))` verwendet.

Über eine Funktion `goal()` könnte man einen ProofNodeSelector auf das aktuelle Goal erzeugen, um den Term der etwa nach einer Regelanwendung an derselben Stelle steht wiederzufinden:

```
match on='f(?x)'
smtSimplify pos=?x
?y = Pos(goal(), termSelector(?x))
```

Überlegung war es ebenfalls, bei der Erzeugung von Positionen implizit `goal()` als ProofNodeSelector anzunehmen, da es möglicherweise das einzig sinnvolle ist.

## 3. Speichern von einem TermSelector-Term-Paar

Die Idee hierbei ist, die ursprüngliche Variante des Matchings wie in 1. eines Terms allein durch das hinzuspeichern eines TermSelectors zu erweitern. Damit würde das Beispiel funktionieren, da bei unklarheiten die TermSelector-Information beachtet wird.

Nachteil kann allerdings sein, dass sich mittlerweile die Sequenz zwischen Zuweisung und Verwendung der Variablen verändert hat, sodass an der Stelle, die der `TermSelector` des Paares angibt, sich der `Term` des Paares gar nicht mehr befindet.

Vorteil ist, dass Falls der Term gerade eindeutig auf der Sequenz zu finden ist, aber mittlerweile an einer anderen Stelle, kann mit `?var` immernoch die richtige Position ausgewählt werden.

Das wäre auch möglich mit der 2. Variante, allerdings ein wenig umständlicher, etwa so: `applyEq on=get(?var) [...]` statt `applyEq on=?var [...]`.

## Benennung von Variablen

Eine weitere Fragestellung hat sich bei der Benennung und syntaktischen Kennzeichnung der Variablen ergeben. In Matching-Literalen werden Schemavariablen mit einem `?` gekennzeichnet. Idee ist es, dem Nutzer dann diese Variablen unter dem Namen `?var` mit dem escaping-character zur Verfügung zu stellen, sodass Variablen gleich heißen, sowohl in Matching-Literalen und außerhalb.

Man könnte unter Umständen einen Vorteil daraus ziehen, das Fragezeichen nicht mit in den Namen einzubeziehen, um etwa einen semantischen Unterschied aus dem syntaktischen Unterschied von `applyEq on=var` und `applyEq on=?var` zu bekommen, allerdings ist mir noch kein nützlicher semantischer Unterschied eingefallen.

Man gewinnt mit dieser Benennung die mentale Assoziation der Variablen mit den Matching-Literalen.
