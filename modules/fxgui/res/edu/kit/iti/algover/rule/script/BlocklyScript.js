astElemColor = ""

function highlight (elemid) {
    astElemColor = document.getElementById(elemid).style["background-color"]
    document.getElementById(elemid).style["background-color"] = "Red";
}

function unhighlight(elemid) {
    document.getElementById(elemid).style["background-color"] = astElemColor;
}

function setOpenEnd(elemid) {
    document.getElementById(elemid).setAttribute("class", "opengoal");
}

function setClosed(elemid) {
    document.getElementById(elemid).setAttribute("class", "closed");
}