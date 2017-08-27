package edu.kit.iti.algover.refrenceTypes;

/**
 * Target for referencing user input values.
 * <p>
 * One possible usecase are instantiations of quantifiers.
 * {@link #getDescription()} could return
 * "Instantiated from forall" in that case.
 * <p>
 * (together with another reference to the instantiated forall term)
 * <p>
 * Created by Philipp on 27.08.2017.
 */
public class UserInputReferenceTarget extends ReferenceTarget {

    private final String description;

    public UserInputReferenceTarget(String description) {
        this.description = description;
    }

    @Override
    public <R> R accept(ReferenceTargetVisitor<R> visitor) {
        return visitor.visit(this);
    }

    public String getDescription() {
        return description;
    }
}
