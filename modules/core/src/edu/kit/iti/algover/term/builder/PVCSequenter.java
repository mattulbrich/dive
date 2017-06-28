/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.util.Util;

import java.util.Collections;
import java.util.List;
import java.util.ServiceLoader;

/**
 * A PVCSequenter is used to translate a {@link PVC} capturing a
 * {@link SymbexPath} resulting from symbolic execution into a {@link Sequent}
 * that can serve as root within a {@link ProofNode} for a {@link Proof}.
 *
 * Sequentr is not really a word, but means "something that brings into the
 * shape of a sequent."
 *
 * Implementing classes are collected in
 *
 * <pre>
 * META - INF / services / edu.kit.iti.algover.term.builder.PVCSequenter
 * </pre>
 *
 */
public interface PVCSequenter {

    /**
     * The list of all implementations known to the system.
     *
     * Registering works using the {@linkplain ServiceLoader services
     * mechanism}.
     */
    public final static List<PVCSequenter> INSTANCES =
            Collections.unmodifiableList(
                    Util.toList(ServiceLoader.load(PVCSequenter.class)));

    /**
     * Gets the name of the implementation.
     *
     * The name is used in script/config files to select the sequenter.
     * It should be short and not contain spaces nor special characters.
     *
     * @return a constant non-<code>null</code> string.
     */
    String getName();

    /**
     * Gets the descriptive text for this implementation.
     *
     * It is used in menu entries etc.
     *
     * @return a constant non-<code>null</code> string.
     */
    String getDescriptiveName();

    /**
     * Translate the smbolic execution path embedded in a pvc into a logical
     * sequent.
     *
     * @param pathThroughProgram
     * @param makeSymbolTable
     *
     * @return a freshly created sequent.
     * @throws DafnyException
     */
    Sequent translate(SymbexPath pathThroughProgram, SymbolTable makeSymbolTable) throws DafnyException;
}
