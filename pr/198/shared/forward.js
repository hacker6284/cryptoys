// A demo's own URL (scramble/, doubledeal/, megadreifach/) is the
// playroom's demo: there is one implementation of each demo, the one in
// the room. The page loads this script with data-algo="<id>", and it
// replaces itself with ../?algo=<id>, keeping every other query parameter
// and the hash (old ?standalone=1 links land in the room too).
(function () {
    var script = document.currentScript;
    var algo = script && script.getAttribute("data-algo");
    if (!algo) return;
    var params = new URLSearchParams();
    params.set("algo", algo);
    new URLSearchParams(location.search).forEach(function (value, key) {
        if (key !== "algo" && key !== "standalone") params.append(key, value);
    });
    var dest = new URL("../", location.href);
    location.replace(dest.pathname + "?" + params.toString() + location.hash);
})();
