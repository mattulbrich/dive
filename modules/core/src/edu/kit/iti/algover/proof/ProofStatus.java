package edu.kit.iti.algover.proof;

/**
 * The different states a proof object can have, depending on the changes to the Project contents
 */
public enum ProofStatus {
    /** no ScriptAST is loaded, ProofNodeRoot is null.*/
    NON_EXISTING,

    /** script has changed but has not been interpreted yet. */
    CHANGED_SCRIPT,

    /** outdated (a project dependency has invalidated the proof, needs reloading) */
    DIRTY,

    /** script has been run on proof, there remain unclosed branches */
    OPEN,

    /** script has been run on proof, all branches are closed */
    CLOSED,

    /** there was a failure when parsing/executing the script */
    FAILING,

}
