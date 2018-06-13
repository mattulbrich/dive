package edu.kit.iti.algover.smttrans.access;

public class SolverResponse {

    public SolverResponse(Response r, Model m) {
        this.response = r;
        this.model = m;

    }

    public SolverResponse(Response r) {
        this.response = r;
    }

    private Response response;
    private Model model;

    public Response getResponse() {
        return response;
    }

    public Model getModel() {
        return model;
    }

}
