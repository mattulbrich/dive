# Treffen am 18.10.2018

- Milestone Autumn 2018
    - neuer Milestone: erstes Beispielprogramm kann mit AlgoVer verifiziert werden
    - Vorschlag Beispielprogramm: LinkedList
        - Fascade steht schon
        - implementierung fehlt noch
        - ghost variable für die daten (als sequenz)
        - spannend wahrscheinlich die invariante die die liste mit den daten koppelt
        - idee: finden der invariante und implementierung ist teil des beweisprozesses (algover soll unterstützen)
- Unterscheidung MatchingTerm vs. Term
    - Grund aktuelle Implementierung unterscheidet nicht zwischen Termen die auf der Sequenz vorkommen müssen und "freien" Termen
    - Idee: getrennte Parametertypen für beide Fälle um Unterscheidung treffen zu können. "freie" Terme dürfen sich trotzdem auf Sequenz beziehen (evtl durch "Expertenmodes" ein-/ausschaltbar)
    - Jonas implementiert
- Fehlende Tests 
    - Manche Tests waren nicht eingetragen (macht Mattias)
- Refactoring von PRAs kann hoffentlich bald gemerged werden
