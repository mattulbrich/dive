/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

/**
 * The different states a proof object can have, depending on the changes to the Project contents
 *
 *
 *                 NON_EXISTING
 *                       |
 *                       | Proof.setScriptText
 *                       v
 *                CHANGED_SCRIPT
 *                       |  ^
 * Proof.interpretScript |  |
 *                       |  | Proof.setScriptText
 *                       v  |
 *             FAILURE | OPEN | CLOSED
 *
 */
public enum ProofStatus {
    /** Initial state. The proof's root is null.*/
    NON_EXISTING,

    /** script has changed but has not been interpreted yet. */
    CHANGED_SCRIPT,

    /** script has been run on proof, there remain unclosed branches */
    OPEN,

    /** script has been run on proof, all branches are closed */
    CLOSED,

    /** there was a failure when parsing/executing the script */
    FAILING,

}

