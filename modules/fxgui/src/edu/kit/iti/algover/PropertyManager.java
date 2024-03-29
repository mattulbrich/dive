package edu.kit.iti.algover;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.*;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.util.ObservableValue;
import edu.kit.iti.algover.util.TypedBindings;
import javafx.beans.property.*;

/**
 * This class holds all relevant properties for the FXGUI.
 * It is implemented as a Singleton so to access properties the getInstance() method is used.
 * @author Jonas Klamroth (08/2020)
 */
public class PropertyManager {

    /**
     * The singleton instance
     */
    private static PropertyManager instance;

    /**
     * the {@link ProofNodeSelector} pointing to the {@link ProofNode} that is currently displayed in the sequent view
     * this selector is bound bidirectionally with {@link PropertyManager#currentProofNode} so updates to either one of
     * them will be mirrored by the other one
     */
    public final SimpleObjectProperty<ProofNodeSelector> currentProofNodeSelector = new SimpleObjectProperty<>();

    /**
     * The {@link ProofNode} that is currently displayed in the sequent view
     * it is bound bidirectionally with {@link PropertyManager#currentProofNodeSelector} so updates to either one of
     * them will be mirrored by the other one
     */
    public final SimpleObjectProperty<ProofNode> currentProofNode = new SimpleObjectProperty<>();

    /**
     * The proof that is currently displayed (corresponding to the selected PVC and seen in the Scriptview as script)
     * This property is bound bidirectionally to the {@link PropertyManager#currentPVC}.
     */
    public final SimpleObjectProperty<Proof> currentProof = new SimpleObjectProperty<>();

    /**
     * The PVC that is currently selected (via breadcrumbbar or via browser view).
     * This property is bound bidirectionally to the {@link PropertyManager#currentProof}.
     */
    public final SimpleObjectProperty<PVC> currentPVC = new SimpleObjectProperty<>();

    /**
     * The file that is currently display in the editorview.
     */
    public final SimpleObjectProperty<DafnyFile> currentFile = new SimpleObjectProperty<>();

    /**
     * The currently loaded project.
     */
    public final SimpleObjectProperty<Project> currentProject = new SimpleObjectProperty<>();


    /**
     * Whichever Term was clicked to apply rules to.
     */
    public final SimpleObjectProperty<TermSelector> selectedTerm = new SimpleObjectProperty<>();

    /**
     * Whichever Term was clicked to reveal dependencies.
     * (Currently set when control-clicking something on the sequent).
     */
    public final SimpleObjectProperty<TermSelector> selectedTermForReference = new SimpleObjectProperty<>();

    /**
     * The proofStatus of the {@link PropertyManager#currentProof}. This property is automatically updated whenever the
     * currentProof is changed. Note however that it is not automatically synchronized with the backend. Thus whenever
     * the interpreter is called for the current proof this property has to be set again.
     */
    public final SimpleObjectProperty<ProofStatus> currentProofStatus = new SimpleObjectProperty<>();

    public final SimpleObjectProperty<ProjectManager> projectManager = new SimpleObjectProperty<>();

    /**
     * Representing the current position of the timeline.
     */
    public final IntegerProperty currentlyDisplayedView = new SimpleIntegerProperty(0);

    /**
     * ChangeListener that binds the back end representation of the proof staus
     * to the status of the currently selected proof.
     */
    public final ObservableValue.ChangeListener<ProofStatus> proofStatusSyncer =
            (observableValue, oldValue, newValue) -> {
        currentProofStatus.set(newValue);
    };

    /**
     * Provides the singleton for this class
     * @return an instance of this class
     */
    public static PropertyManager getInstance() {
        if (instance == null) {
            instance = new PropertyManager();
        }
        return instance;
    }

    private PropertyManager() {
        TypedBindings.bindBidirectional(currentProofNode, currentProofNodeSelector,
                (proofNode -> {
                    if(proofNode != null) {
                        return new ProofNodeSelector(proofNode);
                    }
                    return null;
                }),
                proofNodeSelector -> {
                    if (proofNodeSelector != null) {
                        try {
                            return proofNodeSelector.get(currentProof.get());
                        } catch (RuleException e) {
                            e.printStackTrace();
                        }
                    }
                    return null;
                });
        TypedBindings.bindBidirectional(currentProof, currentPVC,
                proof -> {
                    if(proof != null) {
                        return proof.getPVC();
                    }
                    return null;
                },
                pvc -> {
                    if(pvc != null) {
                        return projectManager.get().getProofForPVC(pvc.getIdentifier());
                    }
                    return null;
                });
        TypedBindings.bind(currentProof, currentProofStatus,
                (proof -> {
                    if(proof != null) {
                        return proof.getProofStatus();
                    } else {
                        return ProofStatus.NON_EXISTING;
                    }
                })
        );


        TypedBindings.bind(currentProof, currentProofNode,
                (proof -> {
                    if (proof != null) {
                        return proof.getProofRoot();
                    }
                    return null;
                })
        );

        // TODO: review Proof and maybe use beans/fx properties.
        currentProof.addListener(((observable, oldValue, newValue) -> {
            if (oldValue != null) {
                oldValue.removeProofStatusListener(proofStatusSyncer);
            }
            if (newValue != null) {
                newValue.addProofStatusListener(proofStatusSyncer);
            }
        }));


        currentPVC.addListener(((observable, oldValue, newValue) -> selectedTermForReference.set(null)));
        currentPVC.addListener(((observable, oldValue, newValue) -> selectedTerm.set(null)));

        selectedTerm.addListener((observable, oldValue, newValue) -> {
            if (newValue != null) {
                if (!newValue.isValidForSequent(currentProofNode.get().getSequent())) {
                    selectedTerm.set(oldValue);
                }
            }
        });

        currentProofNode.addListener((observable, oldValue, newValue) -> {
            if (newValue != null && selectedTerm.get() != null && !selectedTerm.get().isValidForSequent(newValue.getSequent())) {
                selectedTerm.set(null);
            }
        });
    }
}

