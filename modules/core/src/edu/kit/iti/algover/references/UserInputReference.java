package edu.kit.iti.algover.references;

/**
 * Reference for user input values.
 * <p>
 * One possible use case are instantiations of quantifiers.
 * {@link #getDescription()} could return
 * "Instantiated from forall" in that case.
 * <p>
 * (together with another reference to the instantiated forall term)
 * <p>
 * Created by Philipp on 27.08.2017.
 */
public class UserInputReference extends Reference {

    private final String description;

    public UserInputReference(String description) {
        this.description = description;
    }

    @Override
    public <R> R accept(ReferenceVisitor<R> visitor) {
        return visitor.visit(this);
    }

    public String getDescription() {
        return description;
    }

    @Override
    public String toString() {
        return "UserInputReference{" +
                "description='" + description + '\'' +
                '}';
    }
}
