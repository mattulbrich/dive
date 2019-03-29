/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import java.io.File;
import java.util.*;
import java.util.stream.Collectors;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyDeclPVCCollector;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.rules.DafnyRuleUtil;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.impl.DafnyRule;
import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.term.FunctionSymbol;
import nonnull.DeepNonNull;
import nonnull.NonNull;
import nonnull.Nullable;


// REVIEW: I miss a possibility to retrieve all parsed DafnyTrees (toplevel entities)
// How can one obtain these?

// SaG: by getting all PVCCollections from Map pvc and rertieving tree by
// PVCCollection.getDafnyDecl().getRepresentation()



/**
 * Class representing a project, that contains all relevant information for a
 * project that should be verified
 *
 * @author Created by sarah on 8/3/16.
 * @author revised by mattias
 */
public final class Project {

    /**
     * The base directory under which all files must be located.
     */
    private final File baseDir;

    /**
     * List containing references to all problem files
     * All imported libraries
     */
    private final List<DafnyFile> dafnyFiles;

    /**
     * Settings of Project
     */
    private final ProjectSettings settings;

    /**
     * Lookup maps to get Dafny classes of the project-
     */
    private final Map<String, DafnyClass> classes;

    /**
     * Lookup maps to get Dafny toplevel methods of the project-
     */
    private final Map<String, DafnyMethod> methods;

    /**
     * Lookup maps to get Dafny toplevel functions of the project-
     */
    private final Map<String, DafnyFunction> functions;

    /**
     * Lookup maps to get the {@link FunctionSymbol}s corresponding
     * to the functions and fields of the project.
     * <p>
     * Lazily created.
     */
    private Collection<FunctionSymbol> functionSymbols;

    /**
     * The tree data structure for all {@link PVC}s.
     * <p>
     * Lazily created.
     */
    private PVCGroup pvcRoot;

    /**
     * A map from identifier to {@link PVC}.
     *
     * Lazily created.
     */
    private Map<String, PVC> pvcByName;

    /**
     * A collection of all proof rules available in this project.
     *
     */
    private @Nullable Collection<ProofRule> allProofRules;

    /**
     * A collection of all builtin proof rules available in this project.
     *
     */
    private Collection<ProofRule> builtinProofRules;

    /**
     * A collection of all lemmas available in this project.
     *
     */
    private Collection<ProofRule> lemmaProofRules;


    /**
     * Constructor can only be called using a ProjectBuilder
     *
     * @param pBuilder
     * @throws DafnyException
     */
    public Project(ProjectBuilder pBuilder) throws DafnyException {
        this.settings = pBuilder.getSettings();
        this.dafnyFiles = pBuilder.getFiles();
        this.classes = DafnyDecl.toMap(pBuilder.getClasses());
        this.functions = DafnyDecl.toMap(pBuilder.getFunctions());
        this.methods = DafnyDecl.toMap(pBuilder.getMethods());
        this.baseDir = pBuilder.getDir();
        this.pvcByName = new HashMap<>();
        this.allProofRules = null;
    }

    public File getBaseDir() {
        return baseDir;
    }

    public Collection<DafnyFunction> getFunctions() {
        return functions.values();
    }

    public DafnyFunction getFunction(String name) {
        return functions.get(name);
    }

    public Collection<DafnyMethod> getMethods() {
        return methods.values();
    }

    public DafnyMethod getMethod(String name) {
        return methods.get(name);
    }

    public Collection<DafnyClass> getClasses() {
        return classes.values();
    }

    public Collection<ProofRule> getAllProofRules() {
        if(allProofRules == null) {
            allProofRules = Collections.unmodifiableList(makeAllProofRule());
        }
        return allProofRules;
    }

    public Collection<ProofRule> getLemmaProofRules() {
        if(lemmaProofRules == null) {
            lemmaProofRules = Collections.unmodifiableList(makeLemmaProofRules());
        }
        return lemmaProofRules;
    }

    public Collection<ProofRule> getBuiltinProofRules() {
        if(builtinProofRules == null) {
            builtinProofRules = Collections.unmodifiableList(makeBuiltinProofRules());
        }
        return builtinProofRules;
    }

    /**
     * Get the list of available rules for a particular PVC.
     *
     * The set of availbe rules differs between the PVCs since a lemma
     * cannot be used to prove itself on the logic level.
     *
     * (Mutually) recursive lemmas need to be referenced from within their
     * code thus providing a proof which is guaranteed wellfounded.
     *
     * <h4>Examples</h4>
     * <pre>
     *     lemma l1() ensures 1 == 0 { }
     * </pre>
     * We are not allowed to prove l1 using the lemma itself.
     *
     * <pre>
     *     lemma l1() ensures false { }
     *     lemma l2() ensures false { }
     * </pre>
     * Excluing l1 in the proof of l1 does not suffice. Here we also must break
     * the cyclic situation in which l2 proves l1 and l1 proves l2. Hence
     * l1 must not have a forward reference to l2.
     *
     * @author m. ulbrich
     *
     * @param pvc the PVC for which the set of available rules is to be computed.
     *
     * @return the (possibly immutable) set of rules available to the proof of pvc.
     */
    public @DeepNonNull Collection<ProofRule> getProofRules(@NonNull PVC pvc) {
        DafnyDecl decl = pvc.getDeclaration();
        if (!(decl instanceof DafnyMethod)) {
            // (*) if not proving lemma: all lemmas are allowed.
            return getAllProofRules();
        }

        DafnyMethod method = (DafnyMethod) decl;
        if(!method.isLemma()) {
            // see (*).
            return getAllProofRules();
        }

        // otherwise: Filter all lemmas that are behind the currently proven one.
        List<ProofRule> result = new ArrayList<ProofRule>();
        // if true, we have passed the current lemma: do not add anymore
        boolean noLemmas = false;
        for (ProofRule proofRule : getAllProofRules()) {
            if(proofRule instanceof DafnyRule) {
                if(!noLemmas) {
                    DafnyMethod lemma = ((DafnyRule) proofRule).getMethod();
                    // make noLemmas true if we hit the target method.
                    noLemmas = lemma == method;
                }
                if (noLemmas) continue;
            }

            result.add(proofRule);
        }

        return result;
    }


    /**
     * Gets a class from this project by name.
     *
     * @param classname
     *            the non-<code>null</code> classname
     * @return the class named <tt>classname</tt>, or <code>null</code> if not
     *         existing
     */
    public DafnyClass getClass(String classname) {
        return classes.get(classname);
    }

    public List<DafnyFile> getDafnyFiles() {
        return dafnyFiles;
    }

    public ProjectSettings getSettings() {
        return settings;
    }

    @Override
    public String toString() {
        StringBuilder s = new StringBuilder();
        s.append("Project(");
        s.append(this.classes.size() + " classe(s), ");
        s.append(this.methods.size() + " method(s))");

        return s.toString();
    }

    /**
     * Return all PVCs of the project.
     *
     * @return the PVCs as tree data structure.
     */
    public @NonNull PVCGroup getAllPVCs() {
        ensurePVCsExist();
        return pvcRoot;
    }

    /**
     * Generates the PVCs for this project. Saves the PVCs to the String lookup
     * map.
     * <p>
     * This is not thread-safe, but can be made so easily.
     */
    private PVCGroup ensurePVCsExist() {

        if (pvcRoot != null) {
            return pvcRoot;
        }

        PVCGroup root = new PVCGroup(null);

        DafnyDeclPVCCollector visitor = new DafnyDeclPVCCollector(this);
        for (DafnyFile file : this.getDafnyFiles()) {
            visitor.visitFile(file, root);
        }

        pvcByName = new HashMap<>();
        for (PVC pvc : root.getContents()) {
            pvcByName.put(pvc.getIdentifier(), pvc);
        }

        this.pvcRoot = root;
        return root;

    }

    /**
     * Gets a map from identifiers to project PVCs.
     *
     * @return an unmodifiable map.
     */
    public @NonNull Map<String, PVC> getPVCByNameMap() {
        ensurePVCsExist();
        return Collections.unmodifiableMap(pvcByName);
    }

    /**
     * Get the PVCs for a DafnyDecl as tree.
     *
     * @param decl the declaration to look up
     * @return the corresponding PVC collection
     * @throws NoSuchElementException if the declaration is not known
     */
    public PVCCollection getPVCsFor(DafnyDecl decl) {
        ensurePVCsExist();
        PVCCollection result = getPVCsFor(decl, pvcRoot);
        if(result == null) {
            throw new NoSuchElementException();
        }
        return result;
    }

    private PVCCollection getPVCsFor(DafnyDecl decl, PVCCollection g) {
        if (g.getDafnyDecl() == decl) {
            return g;
        }
        for (PVCCollection child : g.getChildren()) {
            PVCCollection result = getPVCsFor(decl, child);
            if (result != null) {
                return result;
            }
        }
        return null;
    }

    /**
     * Gets a PVC by identifier.
     *
     * @param name
     *            the identifier to look up
     * @return the created PVC with the name, or <code>null</code> if that
     *         identifier has no PVC assigned to it.
     */
    public PVC getPVCByName(String name) {
        ensurePVCsExist();
        return pvcByName.get(name);
    }

    /**
     * Gets the all declared functions symbols.
     * <p>
     * These are triggered by field and function declarations.
     *
     * @return the unmodifiable collection of all declared symbols
     */
    public Collection<FunctionSymbol> getAllDeclaredSymbols() {
        if (functionSymbols == null) {
            functionSymbols = DeclarationSymbolCollector.collect(this);
        }

        return Collections.unmodifiableCollection(functionSymbols);
    }


    /**
     * This method creates all the rules available in this project.
     * This is lazily evaluated if needed only.
     */
    private List<ProofRule> makeAllProofRule() {
        List<ProofRule> result = new ArrayList<>();
        if (lemmaProofRules == null) {
            result.addAll(makeLemmaProofRules());
        } else {
            result.addAll(lemmaProofRules);
        }

        if (builtinProofRules == null) {
            result.addAll(makeBuiltinProofRules());
        } else {
            result.addAll(builtinProofRules);
        }        
        return result;
    }

    /**
     * This method creates the lemmas available in this project.
     * This is lazily evaluated if needed only.
     */
    private List<ProofRule> makeLemmaProofRules() {
        List<ProofRule> result = new ArrayList<>();
        // Extract rules from the lemmas.
        try {
            result.addAll(DafnyRuleUtil.generateDafnyRules(this));
        } catch (DafnyException e) {
            // FIXME FIXME ... exception concept needed here
            e.printStackTrace();
        }
        return result;
    }

    /**
     * This method creates the builtin rules available in this project.
     * This is lazily evaluated if needed only.
     */
    private List<ProofRule> makeBuiltinProofRules() {
        List<ProofRule> result = new ArrayList<>();
        ServiceLoader<ProofRule> loader = ServiceLoader.load(ProofRule.class);
        loader.forEach(result::add);
        return result;
    }

    /**
     * Returns all project details necessary for saving and showing in Settings Pane as partial Configuration
     * @return
     */
    public Configuration getConfiguration() {
        Configuration c = getSettings().getConfiguration();
        List<File> dfyFiles = getDafnyFiles().stream()
                .filter(dafnyFile -> !dafnyFile.isInLibrary())
                .map(dafnyFile -> new File(dafnyFile.getFilename()))
                .collect(Collectors.toList());
        c.setDafnyFiles(dfyFiles);

        List<File> libFiles = getDafnyFiles().stream()
                .filter(dafnyFile -> dafnyFile.isInLibrary())
                .map(dafnyFile -> new File(dafnyFile.getFilename()))
                .collect(Collectors.toList());;
        c.setLibFiles(libFiles);

        return c;
    }
}
