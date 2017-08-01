package edu.kit.iti.algover.proof;

/**
 * The different states a proof object can have, depending on the changes to the Project contents
 */
public enum ProofStatus {
    NON_EXISTING, //no ScriptAST is loaded, ProofNodeRoot is null
    NOT_LOADED, //ProofNoderoot is null
    DIRTY, //outdated (a project dependency has invalidated the proof, needs reloading )
    OPEN, //proof is not closed yet
    CLOSED, //proof is closed
    FAILING //there was a failure when loading proof or script

}
