import codeql.actions.security.CachePoisoningQuery

from LocalJob job, Event event
where hasDefaultBranchCacheWriteAccess(job, event)
select job, event
