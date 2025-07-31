-- Structural Session Pi

-- the types
ch   : Type
proc : Type


-- Processes
EndP   : proc
WaitP  : ch -> proc -> proc 
CloseP : ch -> proc -> proc
ResP   : (bind ch,ch in proc) -> proc 
ParP   : proc -> proc -> proc 
InSP   : ch -> (bind ch in proc) -> proc 
DelP   : ch -> ch -> proc -> proc
