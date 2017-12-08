# Tagging von Top-Level-Formeln

Die Idee war etwas wie _Gruppierung_ von Formeln (Top-Level-Formeln) möglich zu machen. Aber ein Baum zu speichern erlaubt nicht so viel Flexibilität wie das _Taggen_ von Formeln. Außerdem wäre es einfacher automatisch Tags einzubauen und den Nutzer erst danach die Gruppierung anhand der Tags wählen zu lassen.

## Beispiel Getaggte Formeln

* `a != null` `#path`
* `a.Length > 15` `#path` `#assert`
* `a.Length > 3` `#path` `#irrelevant`

## Beispiel Getaggte Formeln nach Gruppierungen `#irrelevant` und `#path > #assert`

(Siehe zu Gruppierungen auch _Nutzung von Tags 2._)

Jede der Baumknoten ist auf- und Zuklappbar, wie in TreeViews üblich.

* #path
  * `a != null`
  * #assert
    * `a.Length > 15`
* #irrelevant (normalerweise vom Nutzer zugeklappt)
  * `a.Length > 3`

Für dieses Beispiel scheint die Gruppierung natürlich völlig Überflüssig, aber bei Sequenzen, welche deutlich mehr Formeln haben, ist das Verhältnis Knoten : Blätter deutlich kleiner.

## Generierung von Tags

1. ### Durch den Sequenter
Man taggt automatisch Formeln mit "#pre", "#path" oder "#assert" durch den Sequenter, sodass Formeln, welche von den Preconditions, Pathconditions oder von Asserts abstammen passend markiert werden.
- ### Durch das Markieren von Formeln auf der Sequenz
Per Multi-selection kann der Nutzer auf der Sequenz mehrere Formeln auswählen und als "#irrelevant" markieren und später diese in eine zusammengeklappte Gruppe aussortieren, sodass ihm diese nicht mehr angezeigt wird.
- ### Durch Regelanwendung
Der Nutzer kann alle Formeln, welche durch z.B. eine cut-Regel auf die Sequenz kamen, mit dem Tag "#cut" versehen.
- ### Durch Markierung von Code und allen dazu relevanten Formeln
Der Nutzer markiert einen Teil des Codes und AlgoVer sucht nach allen Referenzen von Code zur Sequenz. Alle "relevanten" Formeln in der Sequenz werden jetzt durch einen vom Nutzer eingegebenen Tag versehen.
- ### Aus Regelanwendungen
Wird eine Formel durch eine Regel aus einer Formel mit dem Tag "#path" erzeugt, dann erbt diese Formel das Tag "#path". Hat eine Formel durch eine Regel mehrere Kinder, vererbt sie alle ihre Tags an alle ihre Kinder. Hat eine Formel mehrere Eltern, erbt sie die Vereinigung aller Tags aller Eltern.

## Nutzung von Tags

1. Die Tags sollten auf der Sequenz (farblich) anzeigbar gemacht werden.
- Außerdem sollte der Nutzer die Möglichkeit haben, aus den Tags auf- und zuklappbare Gruppen zu erzeugen. So kann er z.B. die Priorität der Tags als "#path > #assert" definieren. Dann wird eine Gruppe mit allen Formeln, die das "#path" Tag haben erstellt, in welcher wieder die Formeln die noch zusätzlich das "#assert" Tag haben von dem Rest getrennt wird.
- Diese Gruppierungskonfiguration sollte wohlmöglich am besten auf Proof-ebene gespeichert sein, da sie sich wahrscheinlich nicht über den Beweis hinweg ändern sollte (man möchte eher mit einer bestimmten Gruppierungskonfiguration die anderen Zweige nach relevanten Formeln durchsuchen). Sie sollte allerdings einfach austauschbar und kopierbar zu anderen Beweisen sein.

## Technische Realisierung

Im Model der Formeln sollte ein Set an Tags (Strings) gespeichert werden. Die Farbe kann man als Index in einem Array an Farben abhängig vom Hash des Tagnamens ermitteln (sodass zwei gleichnamige Tags "überall" gleich aussehen und man die Farbe automatisch mit diesem Wort assoziiert).

Wo die Tagerzeugung eingebaut wird ist noch nicht sicher. Man muss sie irgendwie serialisieren können. Zuerst war das Skript dafür angedacht, allerdings bin ich (Philipp) mir nicht sicher, dass das der richtige Ort dafür ist. Das Skript sollte lesbar bleiben und nicht mit für den Beweisverlauf irrelevanten "regeln", bzw. commands überladen werden. Allerdings weiß ich auch keinen besseren Ort für die Serialisierung...

Für die Serialisierung der Gruppierungskonfiguration könnte man eine neue Datei einführen, welche "Viewmodel" relevante Informationen auf Proof-ebene speichert. Vielleicht kann man hier, anstatt im Skript, auch die Tags an sich speichern, allerdings bin ich mir noch nicht sicher, wie man mit der Änderung des Skriptes dann umgehen soll.

(Zu: Vererbung von Tags bei Regelanwendung)
Die Tags zu vererben löst einige Probleme, die mir noch aufgefallen sind:
1. Es wäre für den Nutzer ärgerlich, würde die Applikation immer die Tags der Formeln vergessen, sobald eine Regel auf diese Angewendet wird. Dann müsste der Nutzer jedes mal die Formeln neu "taggen".
- Hat man nur Gruppen, so ist es nicht klar, in welche Gruppe eine Formel kommt, falls man zwei Formeln aus verschiedenen Gruppen kombiniert.

Vererbung von Tags lösen beide Probleme:
Formeln verlieren durch die Vererbung offensichtlich ihre Tags nicht (bei Regelanwendungen) und dadurch, dass der Nutzer eine Gruppenkonfiguration angibt, ist es auch immer eindeutig, in welche Grupper die neue Formel angezeigt und "eingeordnet" werden muss (und es ist durch den Nutzer spezifiziert).
