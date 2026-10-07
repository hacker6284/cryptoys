// A demo's own URL (scramble/, doubledeal/, megadreifach/) is the playroom's
// demo: the page loads this with data-algo="<id>" and it replaces itself with
// ../?algo=<id>, keeping every other query parameter and the hash.
{
    const q = new URLSearchParams(location.search);
    q.delete("algo");
    q.delete("standalone");
    const algo = document.currentScript.getAttribute("data-algo");
    location.replace(`../?${new URLSearchParams([["algo", algo], ...q])}${location.hash}`);
}
