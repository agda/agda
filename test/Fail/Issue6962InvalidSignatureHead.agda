module Issue6962InvalidSignatureHead where

-- Ordinary signatures retain the same validation of the declaration head.
bad (λ x → x) : Set
