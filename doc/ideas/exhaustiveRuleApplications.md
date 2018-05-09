# Exhaustive Anwendung von Regeln

Idee: Es sollte möglich sein Regeln recursive auf einen Term anzuwenden so lange es geht. Wir nennen das 'exhaustive'.

Beispiel:
 ```
 let b1 := true :: let b2 := false :: b2 ==> b1
 ```

sollte wenn man die Regel let-Substitution exhaustive anwendet wie folgt aussehen:

```
false ==> true
```

## Parameter

Die Anwendung von Regeln auf diese Art und Weise ist in verschiedenen Varianten denkbar. Bis jetzt haben wir folgende Parameter festgestellt:
* deep vs. shallow: Dieser Parameter beschreibt ob die Regel nur weiter angewendet wird, so lange die letzte Anwedung erfolgreich (shallow) war oder ob die Regel in jedem Fall auf alle Kindknoten angewendet wird (deep). 
* all vs. selective: Dieser Parameter beschreibt ob die Regel nur auf einen bestimmten Term angewendet wird (selective), oder ob sie auf einer kompletten Sequenz überall wo es es möglich ist angewendet wird (all). 

## Implementierung
Es standen mehrer Möglichkeiten der Umsetzung im Raum:
* ExhaustiveProofRule als Unterklasse von ProofRule die entsprechende Methodik zur Verfügung stellt
* Methode 'applyRuleExhaustive' in RuleApplicator

Aktuell umgesetzt ist die zweite Methode, da es bei der anderen das Problem gibt, dass Regeln selbst keine Veränderung auf der Sequenz vornehmen sondern nur ProofRuleApplications generieren, die alle Änderungsinformationen enthalten. Aus diesem Grund können aber in den ProofRules die Auswirkungen einer ersten Anwendung der Regel nicht erkannt werden und somit sind auch keine auf einer derart entstandenen Sequenz möglich. 

## ScriptGeneration vs. ScriptCommand
Eine weitere Diskussion war ob es einen expliziten Scriptbefehl geben sollte, der diese Art der Anwedung ermöglicht, oder ob alle Regelanwendungen einzeln im Script zu sehen sein sollten. Vorteil eines ausgeschriebenen Scripts ist die Nachvollziebarkeit ist deutlicher besser, da der Nutzer Schritt für Schritt erkennen kann, wie die Sequenz entstanden ist. Nachteil bei dieser Variante ist, dass die Script potentiell relativ groß und dadruch unübersichtlich werden. 

Entscheidung: 
Nutze einzelne Scriptbefehle und ermögliche falls nötig in der GUI zusammenfassung von gleichartigen Befehlen um Übersichtlichkeit zu erhöhen. 

## Dependencies

Wichtig für die aktuelle Implementierung ist es, dass bei der Anwendung von Regeln (ProofApplicator->ChangeSemisequent) folgende Einschränkungen beachtet werden:
* Falls neue Terme hinzugefügt werden (egal ob Antezedent oder Succedent) werden diese am Ende der Semisequenz eingefügt
* Replacements werden immer derart angewendet, dass der betroffene Term seine Position innerhalb der Semisequent nicht ändert

(wurde entsprechend angepasst)

## Aktueller Stand
Aktuell werden shallow seletive exhaustiv-Anwendungen unterstützt. Für diese gibt es im Backend sowohl eine Methode zur Anwendung einer Regel auf diese Art auf einen bestimmten Term eines bestimmten ProofNodes als auch eine Methode die für eine solche Anwendung ein entsprechendes Script generiert.


